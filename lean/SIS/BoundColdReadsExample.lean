/-
Self-indexed streams in Lean: a cold start's reads against the objects it makes,
by running (bergdb item 007; SIS/BoundColdReads.lean). Not part of the trusted
part: checks by running. Added 2026-11-13.

1. The run of 8 replacements of SIS/BoundT4JavaExample.lean (`runJ 8`), the
   second review's case: the section R(21), R(22) holds 22 versions of 12
   nodes. The lazy startup makes 13 objects, but reads 24: the 22 versions,
   and 2 for the top node.
2. A run of 024-12's tree model (`treeSpec`, merges on) with a section of one
   transaction: the rerun's writer follows a stream pointer, a header and a
   version (2 reads, no object besides the version's); rule 4's top-node
   fallback reads 3 headers. 29 reads, 23 objects.

In both, `coldReadsJ_lazy`'s bound holds (checked).
-/
import SIS.BoundColdReadsTheorems
import SIS.BoundT4JavaExample
import SIS.BoundColdDropJExample

namespace SIS.BoundColdReadsExample

open SIS SIS.Example SIS.BoundT4JavaExample

def S8 : Stream Val (Changes Val) := (runJ 8).S

#guard (lastSp S8, S8.length) == (21, 23)
#guard (sectionNodes S8 (lastSp S8)).length == 12
#guard sectionVersions S8 (lastSp S8) == 22
#guard (lazyStartup specJ S8).next == 13
#guard lazyReads specJ (fun _ => 0) S8 == 24
#guard lazyReads specJ (fun _ => 0) S8 ≤ sectionVersions S8 (lastSp S8) + 2 +
  topHeaderReads specJ S8 (lastSp S8) + 2 * rerunReach specJ S8

open SIS.Tree SIS.Check SIS.BoundColdDropJExample in
/-- BergDB's test, marking, one transaction a section. -/
def alT : Algo BVal Tx :=
  { policy := fun _ _ i _ => i - 1, stillDirty := javaTest (treeSpec ppm), mark := true }

open SIS.Tree SIS.Check SIS.BoundColdDropJExample in
/-- The run of SIS/BoundColdDropJExample.lean, then 40 more puts and two small
transactions. -/
def txsR : List Tx := txs ++
  [{base := 9000, ops := (List.range 40).map (fun j => .put (key (j + 40)) 2)},
   {base := 9500, ops := [.put (key 3) 5, .put (key 70) 5]},
   {base := 9800, ops := [.put (key 75) 6]}]

open SIS.Tree SIS.Check SIS.BoundColdDropJExample in
def ST : Stream BVal Tx := (run (treeSpec ppm) alT txsR).S

open SIS.Tree SIS.BoundColdDropJExample in
#guard (lastSp ST, ST.length) == (9, 11) &&
  (lazyStartup (treeSpec ppm) ST).next == 23 &&
  lazyReads (treeSpec ppm) (fun _ => 0) ST == 29 &&
  (lazyReadsRun (treeSpec ppm) (fun _ => 0) ST).2 == 2 &&
  topHeaderReads (treeSpec ppm) ST (lastSp ST) == 3 &&
  decide (lazyReads (treeSpec ppm) (fun _ => 0) ST ≤ sectionVersions ST (lastSp ST) + 2 +
    topHeaderReads (treeSpec ppm) ST (lastSp ST) + 2 * rerunReach (treeSpec ppm) ST)

end SIS.BoundColdReadsExample
