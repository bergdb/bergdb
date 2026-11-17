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
  medium`: `treeconf.sh medium` (27 traces, with the tree model's check),
  then the contract and the bridge checks on them. night.sh now also copies
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
  by hand on any set). It exports with `treeconf.sh`, so the tree model's
  check (treecheck) runs on the medium tree set too, which no level ran
  before.
- **The Mathlib cache**: level2.sh and contractconf.sh run
  `lake exe cache get` in `lean/contract/` only if `.lake/packages/mathlib`
  is missing, then `lake build`. night.sh copies the main tree's
  `lean/contract/.lake` (7.7 GB) with `cp -cR` (clonefile: 28 s on F53, no
  disk space), falling back to `cp -R`.
- **AGENTS.md's line on the level scripts** names the contract package, since
  level2.sh now needs it and its Mathlib cache. This is outside the
  package's gate's paths (`gate.sh`'s step 4 lists it); the brief asks for it.


# 3. Runs


# 4. State

