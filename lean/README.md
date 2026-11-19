Self-indexed streams in Lean
============================

**Work in progress.** This directory is for developers of BergDB. It is
not part of what a user of BergDB relies on, and not a feature. It holds
the executable model of BergDB's algorithm that Java's runs are checked
against (the trace checkers of `level2.sh` to `level4.sh` and `night.sh`),
the model's test programs, and the parts of the abstract model's proofs
that the contract package uses.

Since 2026-11-18 (bergdb 030-18, Frans's decision of that day, 006-31,
section 1) the old proof line is gone from this directory: the key tree's
proofs (lean/SIS/Tree, about 207,000 lines of proof), the bounds on a cold
start, and the rest of the proofs that nothing kept here uses. They are
at the tag `proofs-2026-11-17`, with this file as it was then, which
describes every file and the status of every theorem. The new proofs are
written from scratch in the Lake package `contract/` (bergdb 030-04),
which imports the files of this package that it needs. Its trace checkers,
`contractcheck` and `bridgecheck`, are built from its files by a third
package, `contractcheck/`, without Mathlib (bergdb 028-24).

The model is that of sis-model.md (bergdb 027-01,
[sis-model.md](../items/027-algorithms/01-docs-2026-11-12/sis-model.md));
how Java is checked against it, 027-01's
[levels.md](../items/027-algorithms/01-docs-2026-11-12/levels.md) and the
trace format, 027-02.


What is here
============

The files and their lines (2026-11-18; the old line had 747 files and
279,136 lines in this package, at the tag `proofs-2026-11-17`):

* SIS/Tree/: 11 files, 3,507 lines (210,119 before).
* SIS/ but SIS/Tree/ and SIS/Proof/: 25 files, 6,950 lines.
* SIS/Proof/: 95 files, 46,058 lines.
* Check/: 8 files, 2,413 lines.
* BergDB/: 11 files, 5,220 lines.
* The roots in this directory (SIS.lean, Check.lean, BergDB.lean and the
  six programs' main files): 9 files, 1,704 lines.
* In all: 159 files, 65,852 lines; the contract package, contract/, has 80
  files and 18,704 lines more.

* **The executable model of the key tree**, SIS/Tree/ (12 files): Val.lean
  (the entry values of the BergDB instance and `blive`), Node.lean (a key
  node as its klongs; the searches; the last version and the halves of a
  split), Pe.lean (the writer since record format 8, PE, "plan, then
  emit": a copy of contract/'s `Contract.PE.peTx`, which bergdb 030-21
  proves, on P and with Java's ids, `Pe.runOps` and `Pe.exec`; the tree
  checker's writer since bergdb 026-25), Exec.lean (the writer of record
  formats 2 to 7, `Tree.exec?`: put, the splits, the delete with the upward
  unlink, LE-b, the take-back and root collapse, the merges, the top node;
  `treeSpec` and the statements of Props.lean are about it), Read.lean (get, scan, the touch), Spec.lean
  (`treeSpec`: the tree as an instance of `Spec`, so that `step` is BergDB
  whole), Inv.lean (the tree's invariants, as a walk that can be run),
  Top.lean (the search through the top nodes' skip pointers), Bound.lean
  (`Dag.dirtyNodeBound`), and Props.lean, MergeProps.lean and
  DeadProps.lean (properties of the tree as definitions of type `Prop`,
  which the checkers and the contract package use; their proofs, where
  there were any, are at the tag). The design: bergdb 024-12.
* **The abstract model**, SIS/: the structure P, the stream, the algorithm
  and its assumptions (Basic.lean, Stream.lean, Algorithm.lean,
  Assumptions.lean, Startup.lean), the physical layer (Phys.lean), handles
  (Handle.lean), reclaim (Reclaim.lean), the startup section's bounds
  (Bound.lean, BoundHeight.lean, BoundT4.lean, BoundT4Java.lean), and the
  examples run by the test programs and by `lake build`'s `#guard`s
  (Example.lean, PhysExample.lean, HandleExample.lean, ReclaimExample.lean,
  HandleReclaimExample.lean, BoundExample.lean).
* **The abstract model's theorems that the contract package uses**, with
  their proofs (SIS/Theorems.lean, PhysTheorems.lean, HandleTheorems.lean,
  ReclaimTheorems.lean, HandleReclaimTheorems.lean, BoundTheorems.lean,
  BoundT4JavaTheorems.lean; the proofs in SIS/Proof/): its bridge (bergdb
  030-07) proves recovery, restarts, lazy reading, eviction with handles
  and reclaim's cut for BergDB's key tree through them. The list is under
  "The theorems" below.
* **The trace checkers**, Check/ and TraceCheck.lean, TreeCheck.lean:
  `tracecheck` (the abstract model against Java's traces, levels 2 to 4,
  `java/stress/conformance.sh`) and `treecheck` (the key tree against
  Java's traces of format 3, `java/stress/treeconf.sh`; its writer is
  Pe.lean's since record format 8).
* **The test programs**: `sistest` (Test.lean), `phystest` (PhysTest.lean),
  `reclaimtest` (ReclaimTest.lean), run by `java/stress/lean-tests.sh`, and
  `treetest` (TreeTest.lean), run by `java/stress/tree-tests.sh`; both are
  steps of `java/night.sh`.
* **The user indexes**, BergDB/ (a library of its own, bergdb 020-29): the
  protocol of release 2026.4's indexes, with its safety and liveness
  proofs. It imports nothing of SIS.
* SIS.lean, Check.lean and BergDB.lean import their libraries' files, so
  that `lake build` checks them all; test-traces/ holds the traces of the
  trace checker's own tests (`test-traces/run.sh`), and the fault test of
  its C-STEP (`test-traces/step-faults.sh`, a step of level 3; bergdb
  030-27).


Build and run
=============

Needs elan (`brew install elan-init`). The toolchain version is in
`lean-toolchain`; elan downloads it on first use. No Mathlib (the
contract package's proofs, `contract/`, have it; its checkers build
without it, `contractcheck/`).

    cd lean
    lake build              # checks every file but the test programs, runs the #guard tests
    lake build BergDB       # the user indexes' library alone (020-29)
    lake exe sistest 20 40  # random runs: 20 seeds, 40 transactions each (7 min)
    lake exe phystest 20 40 # the physical layer on random runs (7 min)
    lake exe reclaimtest 20 30     # reclaim: random runs with cuts (1 min)
    lake exe treetest       # the key tree alone, on small exhaustive cases

The level scripts run `lake build`, `tracecheck` and `treecheck`; the test
programs run unattended in `java/stress/lean-tests.sh` and
`java/stress/tree-tests.sh`, steps of `java/night.sh`. Each program exits
with status 1 and prints "N failures" when a check fails, and the step
fails then. Java's take (`java/stress/TakeCheck.java`, `level2.sh`) is
compared with the model's `javaTake` by the `#guard`s of
SIS/BoundExample.lean, which `lake build` runs.


The theorems
============

`lake build` checks every proof. To see that a theorem depends on nothing
but Lean's standard axioms (no `sorry`), put this in a file, for example
`Axioms.lean`, and run `lake env lean Axioms.lean`; each prints
`[propext, Classical.choice, Quot.sound]`, or a part of it (`LM_cutTo`,
`blive_append`, `blive_sub`, `T3_section`, `T3_restarts` and
`step_eq_fast` need no `Classical.choice`):

    import SIS.Theorems
    import SIS.PhysTheorems
    import SIS.HandleTheorems
    import SIS.ReclaimTheorems
    import SIS.HandleReclaimTheorems
    import SIS.BoundTheorems
    import SIS.BoundT4JavaTheorems
    import Check
    import BergDB
    import SIS.Proof.HandlePin
    import SIS.Proof.HandleLinkPos
    import SIS.Proof.HandleCutRun
    import SIS.Proof.HandleCutT12
    #print axioms SIS.T1_recovery
    #print axioms SIS.T1_crash
    #print axioms SIS.T1_nodes
    #print axioms SIS.T2_restart
    #print axioms SIS.T13_markExact
    #print axioms SIS.T15_closed
    #print axioms SIS.LM_newer
    #print axioms SIS.LM_ruleR
    #print axioms SIS.LM_cutTo
    #print axioms SIS.T1_lazy
    #print axioms SIS.CC_canonical
    #print axioms SIS.T2_lazy
    #print axioms SIS.physRunOK_of_tree
    #print axioms SIS.physRunOK_of_evict
    #print axioms SIS.Check.blive_append
    #print axioms SIS.Check.blive_sub
    #print axioms SIS.Check.bspec_physRunOK
    #print axioms SIS.Check.bspec_tr_handles
    #print axioms SIS.tc_handles
    #print axioms SIS.tr_handles
    #print axioms SIS.t2_handles
    #print axioms SIS.tr_handles_restarts
    #print axioms SIS.tp_handles
    #print axioms SIS.rule4_positions
    #print axioms SIS.rule4Pos_handles
    #print axioms SIS.runPos_handles
    #print axioms SIS.T13_markTouch
    #print axioms SIS.T_cover
    #print axioms SIS.T_latest
    #print axioms SIS.T8_recoverCut
    #print axioms SIS.T12_restartCut
    #print axioms SIS.t9_handles
    #print axioms SIS.t12_handles
    #print axioms SIS.T3_section
    #print axioms SIS.T3_restarts
    #print axioms SIS.T3_reads
    #print axioms SIS.T3_rerun
    #print axioms SIS.T3_bounded
    #print axioms SIS.T3_take_step
    #print axioms SIS.T3_take
    #print axioms SIS.T3_take_restarts
    #print axioms SIS.T3_take_decrease
    #print axioms SIS.T3_take_decrease_restarts
    #print axioms SIS.T3_take_rerun
    #print axioms SIS.T3_take_reads
    #print axioms SIS.T4_debt_java
    #print axioms SIS.T4_debt_java_count
    #print axioms SIS.T4_debt_java_tree
    #print axioms SIS.T4_debt_java_restarts
    #print axioms SIS.T4_debt_java_height
    #print axioms SIS.T4_debt_java_height_count
    #print axioms SIS.Fast.markOf_eq_fast
    #print axioms SIS.Fast.writeAll_eq_fast
    #print axioms SIS.Fast.reachList_eq_fast
    #print axioms SIS.Fast.step_eq_fast
    #print axioms SIS.TopBridge.r4Fast_sound
    #print axioms BergDB.Index.reach_inv
    #print axioms BergDB.Index.index_is_function
    #print axioms BergDB.Index.no_stale_entry
    #print axioms BergDB.Index.build_covers
    #print axioms BergDB.Index.gens_accounted
    #print axioms BergDB.Index.start_accepted
    #print axioms BergDB.Index.gen_fresh
    #print axioms BergDB.Index.locked_phase
    #print axioms BergDB.Index.cleanup_ends
    #print axioms BergDB.Index.build_ends
    #print axioms BergDB.Index.weak_fairness_not_enough
    #print axioms BergDB.Index.no_orphans
    #print axioms BergDB.Index.lock_released
    #print axioms BergDB.Index.build_ends_wf
    #print axioms BergDB.Index.build_ends_weak

What they say, in short (the statements' files say it in full):

* The abstract model: T1 (`T1_recovery`, `T1_crash`, `T1_nodes`) and T2
  (`T2_restart`); T13 (`T13_markExact`): marking gives the same records as
  testing; D closed upward (`T15_closed`).
* The physical layer: lemma M (`LM_newer`, `LM_ruleR`, `LM_cutTo`), T1-L
  (`T1_lazy`), CC and T2-L (`CC_canonical`, `T2_lazy`); `PhysRunOK` from
  `RunOK`, TREE and `LiveAppend` (`physRunOK_of_tree`,
  `physRunOK_of_evict`); `LiveAppend` and `SpecOK.liveSub` for the trace
  checker's `blive` (`blive_append`, `blive_sub`, `bspec_physRunOK`,
  `bspec_tr_handles`).
* Eviction over handles (009): T-CACHE, T-READ, T2-C and T-PIN
  (`tc_handles`, `tr_handles`, `t2_handles`, `tr_handles_restarts`,
  `tp_handles`), and rule 4 by position (`rule4_positions`,
  `rule4Pos_handles`, `runPos_handles`; 005-58).
* Reclaim: T13' (`T13_markTouch`), T8 (`T8_recoverCut`), T12 without
  eviction (`T12_restartCut`), T-COVER and T-LATEST (`T_cover`,
  `T_latest`), and over handles T9 and T12 with eviction (`t9_handles`,
  `t12_handles`).
* Bounds (bergdb item 007): T3 (`T3_section`, `T3_restarts`, `T3_reads`,
  `T3_rerun`, `T3_bounded`) and T3 for BergDB's take (`T3_take_step`,
  `T3_take`, `T3_take_restarts`, `T3_take_decrease`,
  `T3_take_decrease_restarts`, `T3_take_rerun`, `T3_take_reads`); T4's debt
  with BergDB's still-dirty test (`T4_debt_java`, `T4_debt_java_count`,
  `T4_debt_java_tree`, `T4_debt_java_restarts`, `T4_debt_java_height`,
  `T4_debt_java_height_count`).
* The trace checker's fast paths equal the model's definitions
  (Check/Fast.lean, Check/R4.lean).
* The user indexes (BergDB/Index/, 020-29): safety (`index_is_function`
  and the rest of Theorems.lean) and liveness (`cleanup_ends`,
  `build_ends`, `no_orphans`, `lock_released`).

The statements whose proofs went with the old line were dropped too
(Frans, 2026-11-18, 10:20; bergdb 030-18): rule 4 by position after a cut
(`Rule4PosCut_handles`, `RunPosCut_handles`, `runHandlesCutPos`; 005-62) and
the tree properties TP1, TP9, TP17 and TP18 (`KlongsRoundTrip`,
`SearchEqSpec`, `ExecRootOKTree`, `VirtLiveOKTree`). They, their proofs, and
the other old theorems (the key tree's TP7, TP10 and TP11; T4's records and
ends; a cold start's reads, `coldReads_*`; `bounded_startup`) are at the tag
`proofs-2026-11-17`. The other properties of SIS/Tree/Props.lean,
MergeProps.lean and DeadProps.lean stay as definitions of type `Prop`;
TP13 and TP15 are proved (`specOKTree`, `liveAppendTree`,
Check/TreeLive.lean).

What the contract package proves, and from what, is bergdb 030-04 and the
030 items; its gate is `contract/gate.sh`. Its checkers are built without
Mathlib in `contractcheck/` (bergdb 028-24), from `contract/`'s own files
(the package's `srcDir`): `ContractCheck.lean`, `BridgeCheck.lean` and the
files they import, none of which imports Mathlib; a build there fails if
one ever does. The level scripts and `night.sh` build them there, so they
need no Mathlib:

    cd lean/contractcheck
    lake build              # contractcheck and bridgecheck, about 30 s
    ../contract/check.sh small drain   # with the traces of treeconf.sh


Reading Lean
============

Enough to read the trusted part:

* `def f (x : A) : B := ...` defines a function f from A to B. Arguments in
  `{ }` are filled in by Lean; `[DecidableEq V]` says that values of type V
  can be compared.
* `structure` is a record type with named fields; `{ f := 1, g := 2 }`
  builds one, `r.f` reads a field, `{ r with f := 3 }` copies with a change.
* `Option A` is `some a` or `none`. `List A` is a list; `xs.map f`,
  `xs.filter p`, `xs.foldl f a` (a loop), `xs.flatMap f`, `xs.all p`,
  `xs.any p` are the usual list functions. `List.range n` is 0, ..., n-1.
* `match e with | p => ...` is a case analysis. `fun x => e` is a lambda.
* `termination_by n.level` tells Lean why a recursive definition ends: the
  level goes down at each call.
* `Prop` is the type of statements; `∀`, `∃`, `∧`, `∨`, `→` are as in logic.
  A `theorem` is a statement followed by its proof after `:= by`.
* `Bool` values are `true` and `false`; `b = true` turns one into a
  statement.

Two good introductions, if more is wanted: Functional Programming in Lean
(chapters 1 and 2) and Theorem Proving in Lean 4.
