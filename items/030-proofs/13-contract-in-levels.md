# 030-13. The contract's checks in the routine tests

Created 2026-11-17 by Frans Lundberg. Status: open.

The contract's checks (030-04, 030-07, 030-09) run as part of the existing
test levels, so that they keep holding as the code changes. Written by an
agent of coord-1117 ("I" below), the night of 17 to 18 November, on the
branch `030-13-levels`.


# 1. The result

Where each check runs now:

- **`java/before-commit.sh`** (the commit gate): Java's own check of the
  contract, TransCheck, in the unit tests (030-09). No Lean, as before.
- **`java/stress/level2.sh`, step 8b** (new): after step 8's `treeconf.sh`
  runs, it builds the contract package (`lean/contract/`) and runs
  `lean/contract/check.sh small drain` (`contractcheck`, with its fault
  tests `faults.sh` and `faults-top.sh`) and
  `lean/contract/bridge-check.sh small drain` (`bridgecheck`, with its fault
  test `bridge-faults.sh` on a small and a reclaim trace). Quick: 2 seeds;
  full: 10 seeds, as step 8.
- **`java/night.sh`**: `transcheck.sh` (step 2b, 030-09); level2.sh full,
  so step 8b with 10 seeds; and new, step 11b, `java/stress/contractconf.sh
  medium`: `treeconf.sh medium` writes 27 traces (no tree model check:
  section 2), then the contract and the bridge checks on them. night.sh now also copies
  `lean/contract/.lake` into its clone (`cp -c`, a clone on APFS).
- Not in any level: `bridgecheck --model` (the clauses in the model's words,
  about 8 minutes for three sets) and the large set.

The run: see section 3.


# 2. Decisions

- **Level 2 runs the checks inline**, as its step 8 runs `treeconf.sh`: the
  traces are those step 8 has just written; no second export. Reason: the
  brief, and no cost but the checks' own.
- **The night's medium step is a script of its own,
  `java/stress/contractconf.sh SET [seeds]`**, not a function in night.sh.
  Reason: night.sh may not be run tonight; a script can be tried alone (and
  by hand on any set).
- **The medium set's traces are written with no tree check**
  (`treeconf.sh` with `TREECHECK=none`, new; `TREE=1 contractconf.sh` runs
  it). Reason: the old tree model's check (treecheck) of the medium set is
  slow: on F53 at 18:00 to 18:30, under load, a trace of m-d8 took about 10
  minutes, of m-d30 about 18 minutes, and m-d62-1 was still running after 19
  minutes, four at a time; the set would take well over an hour, more than
  half of night.sh's 100 minutes. The night never ran it before (its medium
  step is `conformance.sh medium`, the old trace checker), and D1 is paused;
  the brief asks for the contract checks. The run was stopped and the step
  changed.
- **The Mathlib cache**: level2.sh and contractconf.sh run
  `lake exe cache get` in `lean/contract/` only if `.lake/packages/mathlib`
  is missing, then `lake build`. Its cost, measured in a fresh clone on
  F53 (17:20): 263 s, of which the clones of Mathlib and its six
  dependencies from GitHub and the build of the cache tool are most, and 71 s
  the unpacking of 8,907 files; nothing was downloaded, since F53's
  `~/.cache/mathlib` (448 MB) had them all; on a new machine add that
  download. The result: 7.6 GB in `.lake`. A first `lake build` then builds
  the contract package and the old package `lean/` it depends on (not
  measured; `lean/.lake` was in place). night.sh copies the main tree's
  `lean/contract/.lake` (7.7 GB) with `cp -cR` (clonefile: 28 s on F53, no
  disk space), falling back to `cp -R`.
- **AGENTS.md's line on the level scripts** names the contract package, since
  level2.sh now needs it and its Mathlib cache. This is outside the
  package's gate's paths (`gate.sh`'s step 4 lists it); the brief asks for it.


# 3. Runs


# 4. State

