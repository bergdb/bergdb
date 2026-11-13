/-
Self-indexed streams in Lean: bounds, part 3, the nodes a change makes
unreachable with an assumption that BergDB's writer meets, and a cold start's
reads with it (bergdb item 007; 007-03, step 6; 007-09's second review).

Trusted part: the statements. The definitions they are about are in
SIS/BoundColdDropJ.lean (`DropStepJ`, `DropRunOKJ`, `lostTo`), SIS/BoundCold.lean
(`removedAt`), SIS/BoundHeight.lean (`LiveHeightLe`) and SIS/BoundT4.lean
(`changeAt`); the proofs in SIS/Proof/BoundColdDropJ.lean. Added 2026-11-13.
-/
import SIS.Proof.BoundColdDropJ

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The nodes a change makes unreachable (`removedAt`), with `DropStepJ`: at
most the weights of its entries (for BergDB `bvalW`: one for a key klong, the
compare values of a delete bitmap) plus k, the pointers that the nodes it
makes unreachable lose to nodes it makes unreachable too (BergDB's unlinked
chains and their values). No TREE is needed. Unlike `removedAt_bound`, this
holds for Java's bitmaps and its upward unlink (SIS/BoundColdDropJExample.lean:
`DropStep` fails there, `DropStepJ` holds). -/
theorem removedAt_bound_J (sp : Spec V T) (w : V → Nat) (P : Struct V) (j : Time) (c : Changes V)
    (k : Nat) (hd : DropStepJ sp w P j c k) :
    (removedAt sp P c j).length ≤ (c.adds.map (fun a => w a.2)).sum + k :=
  removedAt_le_J sp w P j c k hd

/-- A cold start's reads after a run, by height, with `DropRunOKJ` in place of
`DropRunOK` (`coldReads_height` with an assumption that Java meets): with
BergDB's still-dirty test, `RunOK`, `LiveAppend`, TREE in the initial
structure and after every transaction, `DropRunOKJ` with weights w and counts
k, and the root's live height at most H after every transaction, the lazy
startup from the run's stream gives out at most

  (the section's index nodes) + (for each transaction T(j) of the section,
  (H + 1) (new nodes + entries + touched nodes + the weights of its entries +
  k j) + its new nodes) + 2

handles. As `coldReads_height`, it counts objects made (handles), not reads. -/
theorem coldReads_height_dropJ (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts)
    (w : V → Nat) (k : Nat → Nat) (hdrop : DropRunOKJ sp al w k ts)
    (H : Nat) (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root) :
    let S := (run sp al ts).S
    (lazyStartup sp S).next ≤ (sectionNodes S (lastSp S)).length +
      ((sectionIdx S (lastSp S)).map (fun j =>
        (H + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          ((changeAt sp al ts j).adds.map (fun a => w a.2)).sum + k j) +
        (changeAt sp al ts j).new.length)).sum + 2 :=
  coldReads_height_dropJ_of sp al ts hok hla hj htree0 htree w k hdrop H hH

end SIS
