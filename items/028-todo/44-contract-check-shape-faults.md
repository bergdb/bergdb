028-44. Change: the contract checker fails a trace with a shape fault
=====================================================================

Status: in progress. Kind: Change. Frans: none.
Created 2026-11-24 by Frans Lundberg.

What: the contract checker, `lean/contract/ContractCheck.lean`, computes
the writer's own rules, `shapeFaults` (`Contract/Shape.lean`: RootsOK,
FillOK, LeftmostOK, DeadOK and BalancedOK), on Java's tree after every
traced transaction and prints their count, `shape faults N [names]`, but
does not fail a trace on it: a trace fails only on C1 to C5, R1, L1, L2,
KIND or the verdict. The change: a trace with a shape fault fails
(CONTRACT FAILED, the rule's name and the first transaction in its line),
and the checker's fault test has a shape fault.

Why: the theorems of the writer's acceptance and of the dirty-node bound
assume the fill rules, `Contract.PE.FillOk`, which is `shapeFaults`
finding no fault (030-38, G8 and G9): a premise tested, not proved. The
tree checker's C-T6 tests it with its own walk (`faultsAt`,
`lean/SIS/Tree/Inv.lean`), BalancedOK only as KindsOK; the contract
checker computes the premise as the theorems state it, but only reports
it (0 faults on every set of `java/night.sh` of 2026-11-23). Failing on it
makes the statement's own definition a check on every contract set.
030-39, finding F6 (section "Actions"); Frans registered it on 2026-11-24
(006-33, point 3).

Frans: none. `ContractCheck.lean` is pinned as a checker's main file
(`lean/contract/pin.sh`), not as a statement: its new hash in
`statements.pin` changes no theorem's statement.

Done when:

* `lean/contract/faults.sh` has a fault that breaks one shape rule and
  nothing else (for instance the TREE line's mb raised so that FillOK
  fails, with C1 to C5 and KIND as before); the checker before the
  change passes that trace (CONTRACT OK), the changed one fails it;
  FAULTS OK.
* The good traces pass: `lean/contract/check.sh` CONTRACT OK on the
  small and drain sets, with `faults-top.sh` and `bridge-faults.sh`.
* `lean/contract/pin.sh`, then `lean/contract/gate.sh` GATE OK (it needs
  Mathlib): `statements.pin` changes in `ContractCheck.lean`'s line only.
* `java/stress/level2.sh` LEVEL 2 OK: its step 0 (`pins.sh`) checks the
  new pin without a build, its step 8b runs `check.sh`.
* The texts: `ContractCheck.lean`'s header (S fails a trace; it is still
  no clause of the contract or of `checkVerdict`), `faults.sh`'s header,
  030-26, 2.1 (the fill rules checked by both checkers). 030-38, the
  guarantees of release 2026.6, stays as it is.

First step: build the checkers (`cd lean/contractcheck && lake build`)
and run `contractcheck` on `lean/contract/test/small.trace` and on the
traces that `faults.sh`, `faults-top.sh` and `bridge-faults.sh` expect to
pass: a shape fault in a hand-made trace is fixed in the trace, not
excused in the checker. Then the function `main` in
`ContractCheck.lean`: the shape count joins the failures that set
`pass`, but stays out of the comparison of `bad` with `checkVerdict`,
the contract's verdict, which has no S; else the checker prints that the
verdict and its counts disagree.


Log
---

2026-11-24. Registered by an agent of lead-1124, from 030-39, F6
(Frans, 2026-11-24, 006-33, point 3).

2026-11-24. Taken by an agent of lead-1124, on the branch `028-44`.
