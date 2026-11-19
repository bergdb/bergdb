028-24. Change: the level scripts without Mathlib
=================================================

Status: done (branch `028-24-checkers-no-mathlib`). Kind: Change. Frans: none.
Created 2026-11-19 by Frans Lundberg.

What: since 030-13, `java/stress/level2.sh` and `java/night.sh` (through
`java/stress/contractconf.sh`) run the contract checkers `contractcheck`
and `bridgecheck`, built in the contract package `lean/contract/`, which
requires Mathlib. Level 2 therefore needed Mathlib's cache and fetched it
over the network when it was missing (on 2026-11-19 it failed on a DNS
error). Find what the checkers take from Mathlib, and build them without
it if that is cheap.

Why: Frans, 2026-11-19, 10:40: "I thought we had no dependency of Lean's
Mathlib." And 10:42: "Yes" (to: check what the contract checkers take from
Mathlib, then split them out if it is cheap). Mathlib was decided on
2026-11-17 for the new proof package only, so that `lean/` and the level
scripts would stay without it.

Frans: none.

Done when: the checkers build and run without Mathlib, in level 2 and
night.sh; the proofs still build with Mathlib (`lean/contract/gate.sh`);
no statement changed; level 2 passes with no `lean/contract/.lake`.


1. What the checkers took from Mathlib
--------------------------------------

The import closure of the two executables (`ContractCheck.lean`,
`BridgeCheck.lean`) was 25 files of `lean/contract/` and 24 of `lean/`.
Of these, only one file imported Mathlib, and only for a proof:

* `contractcheck`: nothing. Its closure (Contract/Tree, Read, Statement,
  Check, Shape, Trace, Complete, Reach, Top, CheckShape, TraceTop, History,
  ShapeStatement, HistoryTop, Verdict, Bridge, Recover, KindsCheck and
  `lean/`'s SIS and Check files) imports only core Lean and Std
  (`Std.Data.HashMap`, `Std.Data.HashSet`).
* `bridgecheck`: `Contract/RecoverCheck.lean` imported `Mathlib.Tactic`
  and `Contract.Proof.BridgeInv` (which imports `Mathlib.Tactic`, and
  through Proof/BridgeMap, Proof/Node and Proof/Frame more of it). The
  checker uses the file's three definitions, `startKindsOk`,
  `kindsStepsOk` and `kindsHistoryOk` (K-LEVEL computed, Bool functions
  over `Std.HashMap` and lists), which use nothing from Mathlib. The
  imports served the file's one theorem, `kindsHistoryOk_meets` (the
  verdict gives `KindsOK`), whose proof uses `BHist.tree_succ` from
  Proof/BridgeInv.lean.

So nothing had to be replaced by a core or Std equivalent: the theorem
moved to a file of its own, and the checkers' closure has no Mathlib.


2. The change
-------------

* `Contract/RecoverCheck.lean` keeps the three definitions, without the
  imports of Mathlib and Proof/BridgeInv. `kindsHistoryOk_meets` moved,
  its text unchanged, to the new file `Contract/RecoverCheckTheorems.lean`
  (with those imports; named as RecoverTheorems.lean and the others), which
  `Contract.lean` imports. Axioms.lean names the theorem as before.
* A new Lake package, `lean/contractcheck/`, without Mathlib: its
  lakefile has `srcDir = "../contract"`, requires `lean/` (path `..`), and
  builds the two executables (default targets) from `lean/contract/`'s own
  files. The files the proofs speak of are the files the checkers run; no
  file moved. A build there fails if a file of the checkers' closure ever
  imports Mathlib, which keeps the closure clean. It builds in about 30 s.
* `lean/contract/lakefile.toml` no longer builds the executables (its
  default target is the library `Contract`, the proofs, with Mathlib).
* The scripts of `lean/contract/` (check.sh, bridge-check.sh, faults.sh,
  faults-top.sh, bridge-faults.sh) run the checkers in
  `../contractcheck/.lake/build/bin/`. `java/stress/level2.sh` and
  `java/stress/contractconf.sh` build them with `lake build` in
  `lean/contractcheck/`, with no `lake exe cache get`; `java/night.sh`
  copies `lean/contractcheck/.lake` into its clone instead of
  `lean/contract/.lake` (8 GB with Mathlib). Only the lines that build or
  run the checkers changed, and the header lines that describe them.
* `pin.sh` pins the new package's lean-toolchain, lakefile.toml and
  lake-manifest.json too; `gate.sh`'s step 4 allows changes in
  `lean/contractcheck/` as in `lean/contract/`.
* AGENTS.md (Code) and lean/README.md say that the level scripts need no
  Mathlib; only the proofs and `gate.sh` do. `lean/contract/` has no
  README of its own; lean/README.md describes the new package.

Why not a path dependency (the first plan: a package holding the checker
files, which `lean/contract/` requires). Lake looks a module up in the
root package first, and a library whose root is `Contract` claims every
module `Contract.*`; so `lean/contract/`'s library would claim the moved
files' modules and not find them. A path dependency needed the checker
files' modules renamed (a new prefix: about 23 files moved and the imports
of most proof files changed) or `lean/contract/`'s library to list its
modules one by one. The shared `srcDir` gives the same separation with
no file moved and no module renamed.


3. The statements
-----------------

No statement changed. The pinned files that changed (statements.pin,
rerun with pin.sh):

* `lean/contract/Contract/RecoverCheck.lean`: the theorem
  `kindsHistoryOk_meets` moved out, its imports of Mathlib and
  Proof/BridgeInv went, its header comment names the new file. The three
  definitions' text did not change.
* `lean/contract/Contract/RecoverCheckTheorems.lean`: new, the theorem's
  text as it was (checked with diff: equal but for a blank line).
* `lean/contract/lakefile.toml`: the two `lean_exe` entries and their
  default targets went.
* `lean/contract/gate.sh`: step 4's allowed paths.
* New pins: `lean/contractcheck/lean-toolchain`, `lakefile.toml`,
  `lake-manifest.json`.


Log
---

2026-11-19. Registered and taken by an agent of coord-1118 (Frans, 10:40
and 10:42), in a clone of the repository.
