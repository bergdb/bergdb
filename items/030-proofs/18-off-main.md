# 030-18. The writer proof off main; the old proofs deleted

Created 2026-11-18 by Frans Lundberg. Status: done.

Frans's decisions of 2026-11-18, 08:42 (006-31, section 1): the writer
proof (030-10, 030-16) is tagged and taken off `main` ("Yes, Tag it and
take it off main."), and the old proof line (D1 of 030's map, frozen at
the tag `proofs-2026-11-17`) is deleted now ("D1, delete the old proofs
now."). What is kept follows 030-04, section 4.1. Done by an agent of
coord-1118 on the branch `030-18-off-main` from `main` 52459c9d, in a
clone; `main` 4a4f9647 (030-19) merged before part 1's final gate.


# 1. Part 1: the writer proof off main

The writer proof is at the tag `writer-proof-2026-11-18` (on 52459c9d).

**Removed** from `lean/contract/`, decided by imports: every file that only
the writer's files and the aggregator `Contract.lean` reach.

* The writer's files: `Contract/Writer.lean`, `WriterBalancedFalse.lean`,
  `WriterExample.lean`, `WriterExample2.lean`, and the 33
  `Contract/Proof/Writer*.lean`.
* Reached only from them (all headed 030-10 or 030-16):
  `Proof/NodeAlg.lean` to `NodeAlg5.lean`, `Proof/TreeCtx.lean`,
  `Proof/Sound.lean`, `Proof/TreeRules.lean`, `TreeRulesChain.lean`,
  `TreeRulesDel.lean`, `TreeRulesMerge.lean`, `TreeRulesSeg.lean`,
  `TreeRulesUp.lean`.
* The checker `WriterCheck.lean`, its exe `writercheck` (lakefile.toml)
  and `writer.sh`.
* Their 41 imports in `Contract.lean`, their 69 lines of `Axioms.lean`
  (195 theorems to 126), and their pins: `statements.pin` rewritten by
  `pin.sh` (79 files pinned; 68 in the main theorems' closure).

In all 51 Lean files and `writer.sh`: `lean/contract/` from 131 files and 58,347 lines to 80
files and 18,640 lines (18,704 with 030-19 merged).

**One file kept needed the writer:** `Proof/Prefix.lean` (030-17, the
klongs cut at a time) imported `Proof/NodeAlg.lean` for four small
definitions and lemmas of W1's check (`tStep`, `headOk`, `timesOk_eq`,
`headOk_append`; 20 lines). They were copied into `Prefix.lean`, which no
longer imports the writer; no statement changed (`Prefix.lean`'s hash in
the pin file changed with it, step 5 lists it).

**Mentions:** `gate.sh`, `check.sh`, `java/stress/level2.sh`,
`java/night.sh` and the READMEs did not mention the writer's files or
`writer.sh`; nothing to change there. 030-10 and 030-16 have a closing
note at the head of their State sections and a log line; the 030 map
(D0, and the rows of 030-10 and 030-16) says where the code is.


# 2. Part 2: the old proofs deleted

**Method.** The import closure of the roots (a script over the `import`
lines of `lean/` and `lean/contract/`); every `.lean` file of the `sis`
package outside it deleted, whole files only; `SIS.lean` rewritten to
import the kept `SIS` modules (185 imports to 131), so that `lake build`
still checks every file kept. The roots:

* the contract package (`Contract`, `ContractCheck`, `BridgeCheck`), as
  part 1 left it;
* the executables the scripts run: `tracecheck` and `treecheck` (level
  scripts, `conformance.sh`, `treeconf.sh`, `contractconf.sh`), `sistest`,
  `phystest` and `reclaimtest` (`lean-tests.sh`), `treetest`
  (`tree-tests.sh`);
* the libraries `Check` (default target) and `BergDB` (the user indexes,
  020-29; not part of the old proof line: kept whole);
* `SIS.BoundExample`: its `#guard`s compare the model's `javaTake` with
  Java's take, which `level2.sh`'s TakeCheck step relies on ("lake build
  compares").

**Removed:** 588 files; the package is 213,284 lines smaller: the key tree's proofs (549 of
lean/SIS/Tree's 560 files), the bounds on a cold start and T4's records
and ends (`BoundCold*`, `BoundColdDrop*`, `BoundT4Theorems` and the rest,
with their `#guard` examples), `bounded_startup`, the proofs of rule 4 by
position after a cut, and 13 files of SIS/Proof/.

**Kept** (159 files, 65,852 lines), and why:

* SIS/Tree/: 11 files, 3,507 lines: the executable model (Val, Node,
  Exec, Read, Spec with `treeSpec`, Inv, Top, Bound) and the `Prop`
  definitions Props, MergeProps and DeadProps, which the checkers and the
  contract package import.
* SIS/ (25 files) and SIS/Proof/ (95 files, 46,058 lines): the abstract
  model and the theorems that the bridge (030-07, 030-14, 030-17) uses:
  T1, T2, the physical layer, handles, reclaim's cut, T3, T4's debt for
  Java's test; each imported, directly or through others, by
  `lean/contract/`. This is most of what stays: the contract's
  `full_recovery`, `full_restart`, `full_eviction` and `full_cut` rest on
  them.
* Check/ (8 files), the six programs' main files, `BergDB/` (11 files).

Statements kept without their proofs (definitions of type `Prop` in files
kept, their proofs deleted; left, as `HandleReclaimTheorems.lean` is
pinned and a statement changes only on Frans's word):
`Rule4PosCut_handles`, `RunPosCut_handles`; Tree/Props.lean's
`KlongsRoundTrip`, `SearchEqSpec`, `ExecRootOKTree`, `VirtLiveOKTree`.
No theorem was cut out of a kept file: whole-file deletion was the lever,
and a kept file's unused theorems are few next to what went.

**Line counts** (`.lean` files):

* `lean/` in all: 878 files, 337,483 lines at 52459c9d; 239 files,
  84,556 lines now.
* The `sis` package (lean/ but contract/): 747 files, 279,136 lines; now
  159 files, 65,852 lines.
* lean/SIS: 719 files, 269,745 lines; now 131 files, 56,515.
* lean/SIS/Tree: 560 files, 210,119 lines; now 11 files, 3,507.
* lean/contract: 131 files, 58,347 lines; now 80 files, 18,704.

**References fixed** (maintained text only):

* `lean/README.md`: rewritten (1,570 lines to 274): what lean/ holds, the
  counts, building and running, the 71 theorems kept with their
  `#print axioms` block (checked: the standard axioms only), the
  statements kept without proofs, and where the old line is.
* 027-11 (startup): `T4_ends`, the cold-start reads (`coldReads_*`,
  `removedAt_bound`, `DropStep`, BoundCold.lean, BoundColdDrop.lean,
  BoundColdDropExample.lean) and rule 4 by position after a cut point to
  the tag. 027-13 (reclaim) and 027-03 (rule 4 by position after a cut):
  the same. 027-02 cites only files kept.
* `java/`: no comment cites a deleted file or theorem (the three that
  name `lean/SIS/Evict.lean` say "until bergdb 005-62", a record). No Java
  file changed. `README.md`: nothing to change.
* Not changed: 027-04 (an outline proposal, a record), older items, and
  the comments inside kept Lean files.

The lakefile's targets did not change: every executable stays.


# 3. The gates

Part 1, the commit 664f4cb0 and main 4a4f9647 merged (051c8a49):

* `lake build` in `lean/` (790 jobs, no change) and in `lean/contract/`:
  passes, no error, no warning in the contract package.
* `lean/contract/gate.sh 4a4f9647`: GATE OK; 126 theorems, the standard
  axioms only; 68 files in the main theorems' closure, 79 pinned; the
  pinned files changed: `Axioms.lean`, `Proof/Prefix.lean`, `lakefile.toml`
  (`pin.sh` run after the merge, whose `statements.pin` conflicted).
* `java/stress/level2.sh` (full): LEVEL 2 OK, before the merge (on
  664f4cb0) and after it (on 051c8a49); step 8b's contract and bridge
  checks on the small (70 traces) and drain (110 traces) sets: no failure.
* No Java file changed: `before-commit.sh` not needed.

GATED 051c8a49.

Part 2, the commit 133eb269 (on 051c8a49; `main` had not moved):

* `lake build` in `lean/` after removing every build product whose source
  is gone (so that nothing can use a deleted module): 202 jobs (790
  before), passes; `lake build sistest phystest reclaimtest treetest
  tracecheck treecheck`: passes; `lake build` in `lean/contract/`: passes.
* `lean/contract/gate.sh`: GATE OK (steps 1, 2, 3 and 5; 126 theorems, the
  pins unchanged: no pinned file was deleted or changed). With the base
  4a4f9647, step 4 lists the files changed outside `lean/contract/`, as
  part 2 must: `lean/SIS.lean`, `lean/README.md`, the deleted files under
  `lean/SIS/`, and 027-03, 027-11, 027-13; nothing else.
* The 71 theorems of `lean/README.md`'s `#print axioms` block: the
  standard axioms only.
* `java/stress/level2.sh` (full): LEVEL 2 OK (TRACECHECK OK 70 and 50,
  TAKECHECK OK, the contract and bridge sets as in part 1).
* `java/stress/level3.sh` (full): LEVEL 3 OK (conformance with reclaim: 35
  traces, TRACECHECK OK, C-CUT 0 of 794 cuts fail).
* `java/stress/level4.sh` (full): LEVEL 4 OK (conformance with eviction: 54
  traces, TRACECHECK OK, C-P and C-H 0 of 14,646 transactions fail).
* Two steps of `night.sh` on the kept test programs:
  `java/stress/lean-tests.sh`: LEAN TESTS OK (`sistest`, `phystest`,
  `reclaimtest`: all checks pass); `java/stress/tree-tests.sh` (`treetest`,
  about 50 minutes on one core) started, 8 of its sets passed with no
  failure, then stopped to save time: its sources and their imports did
  not change, and it builds.
* `java/night.sh` and the scripts it runs: no reference to a deleted file
  (grep of every `.lean` path and `lake` target in `java/` and `lean/`'s
  scripts). No Java file changed.

GATED 133eb269.


# State

2026-11-18. Done: both parts gated and committed on the branch
`030-18-off-main` in the clone of coord-1118's agent rm, for the
coordinator to land. Left for Frans:

* The statements kept without their proofs (section 2): drop them from
  the kept files, or keep them as the record of what the old line proved?
  They are in pinned files (`HandleReclaimTheorems.lean`), so either way a
  statement file changes on his word.
* `BergDB/` (the user indexes' proofs, 020-29) was kept whole: not part of
  the old proof line, which 006-31's D1 names as lean/SIS.
* Comments inside kept Lean files still cite deleted files in places; they
  are records, like the older items.


# Log

2026-11-18. Created; parts 1 and 2 by an agent of coord-1118.
