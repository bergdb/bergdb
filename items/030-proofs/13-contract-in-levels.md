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
  `lean/contract/check.sh small drain` (`contractcheck`, after its fault
  tests `faults.sh` and `faults-top.sh`) and
  `lean/contract/bridge-check.sh small drain` (`bridgecheck`, after its
  fault test `bridge-faults.sh` on a small and a reclaim trace). Quick: 2
  seeds; full: 10 seeds, as step 8. About 3 minutes of the full run.
- **`java/night.sh`**: `transcheck.sh` (step 2b, 030-09); level2.sh full,
  so step 8b; and new, step 11b, `java/stress/contractconf.sh medium`:
  `treeconf.sh medium` writes 27 traces (no tree model check: section 2),
  then the contract and the bridge checks on them; 32 minutes on F53 under
  a heavy load. night.sh now also copies `lean/contract/.lake` into its
  clone (`cp -c`, a clone on APFS: 28 s, no disk space).
- **The checks run four at a time**: `check.sh` and `bridge-check.sh`
  split a set into `PAR` parts (default 4, balanced by bytes) with the new
  `lean/contract/par.sh`, and sum the parts' totals into one `total:`
  line. On the medium set: the contract 1,359 s to 391 s, the bridge
  4,097 s to 1,423 s; the totals are the same.
- Not in any level: `bridgecheck --model` (the clauses in the model's
  words, about 8 minutes for three sets), the large set, and the old tree
  model's check of the medium set.

Both runs pass: LEVEL 2 OK, and CONTRACTCONF OK on the medium set (section
3). No check failed on any trace.


# 2. Decisions

- **Level 2 runs the checks inline**, as its step 8 runs `treeconf.sh`: the
  traces are those step 8 has just written; no second export. Reason: the
  brief, and no cost but the checks' own.
- **The night's medium step is a script of its own,
  `java/stress/contractconf.sh SET [seeds]`**, not a function in night.sh.
  Reason: night.sh is not run tonight; a script can be tried alone (and by
  hand on any set).
- **The medium set's traces are written with no tree check**
  (`treeconf.sh` with `TREECHECK=none`, new; `TREE=1 contractconf.sh` runs
  it). Reason: the old tree model's check (treecheck) of the medium set is
  slow: on F53 at 18:00 to 18:30, under load, a trace of m-d8 took about 10
  minutes, of m-d30 about 18 minutes, and m-d62-1 was still running after 19
  minutes, four at a time; the set would take well over an hour. The night
  never ran it before (its medium step is `conformance.sh medium`, the old
  trace checker), D1 is paused, and the brief asks for the contract checks.
  The run was stopped and the step changed.
- **The checkers run in parts** (`par.sh`), since one `bridgecheck` over the
  medium set took 68 minutes, most of the night's added time. Its time per
  trace grows with the tree: m-mixed 4 s, m-long 13 s, m-r-del 16 s,
  m-long3 67 s, m-fifo 147 s, m-d8 156 s, m-d30 402 s, m-d62 744 s (single
  traces, under load). Not made faster inside the checker: that is 030-07's
  code, shared tonight. PAR stays 4, as treeconf.sh's.
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
  `lean/contract/.lake` (7.7 GB) with `cp -cR` (clonefile), falling back to
  `cp -R`.
- **AGENTS.md's line on the level scripts** names the contract package,
  since level2.sh now needs it and its Mathlib cache. This is outside the
  package's gate's paths (`gate.sh`'s step 4), so it is the branch's last
  commit, apart: the commit before it passes the gate; the coordinator
  decides whether to land the AGENTS.md line.


# 3. Runs

All on F53 in my clone, 2026-11-17, with other agents' runs going (load 15
to 86).

- `java/stress/level2.sh` (full) at 7b979be0, the checks in one part:
  LEVEL 2 OK, 55 minutes (17:05 to 17:59). Step 8b: build 5 s, contract
  78 s, bridge 86 s. Contract: small 70 traces, 7,100 transactions; drain
  110 traces, 13,900 transactions; C1 to C5, R1, L1, L2 no failure, 2.7
  million LIVE lines. Bridge: the same traces, start, N, K, L, A2, A3, A5,
  TREE, TB, TOUCH, A6', COPY no failure.
- `java/stress/contractconf.sh medium`, serial checks: CONTRACTCONF OK,
  93 minutes (export 112 s, contract 1,359 s, bridge 4,097 s). 27 traces,
  13,667 transactions, 736,718 operations, 610,036 nodes made, no failure.
- The same with `par.sh`: CONTRACTCONF OK, 32 minutes (export 75 s,
  contract 391 s, bridge 1,423 s), the same totals.
- `par.sh` tested: on the small set its `total:` line is the one-part
  line, character for character; a trace with a line of an unknown kind
  among 20 fails it (status 1).
- `java/before-commit.sh`: BEFORE COMMIT OK (97 s) at f06ef176.
- `lean/contract/gate.sh 903a228a`: steps 1 to 3 pass (67 theorems, the
  standard axioms); step 4 lists only AGENTS.md (section 2).


# 4. State

