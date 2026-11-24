028-44. Change: the contract checker fails a trace with a shape fault
=====================================================================

Status: done. Kind: Change. Frans: none.
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


Result
------

`lean/contract/ContractCheck.lean` (d4cbb95b):

* `main`: a trace with a shape fault fails (`pass` is false when the
  count `c.shape` is not 0). The count stays out of `bad`, the sum of the
  contract's clauses (C1 to C5, R1, L1, L2 and KIND) that is compared
  with the verdict `checkVerdict`, which has no S: a trace with shape
  faults alone prints no line "the verdict (checkVerdict) is ..., the
  loop's counts say the other".
* `checkTrace`: a shape fault is the trace's first failure if none came
  before it, `first: TX i: S, the writer's rules [names]`; the line's
  `shape faults N [names]` is as before. `check.sh` lists such a trace
  among the failed ones (it finds `first: `).
* The header: S fails a trace, and is no clause of the contract nor of
  the verdict; the verdict is compared with the counts of the contract's
  clauses only.

The traces that the fault tests expect to pass had no shape fault before
the change: `test/small.trace` (TREE without mb, so H, m and theta 0),
faults.sh's good trace (the mixed configuration, 60 transactions,
`TREE 8 1 2 1 2 4 4 2`) and faults-top.sh's (hot, 100 transactions);
bridge-faults.sh runs the bridge checker only. No hand-made trace needed
a fix.

`lean/contract/faults.sh`, the fault `fillmb`: the TREE line's mb, the
writer's m, raised by one (2 to 3): 170 FillOK faults, the first in TX 7,
C1 to C5, R1, L1, L2 and KIND 0, no verdict line; faults.sh checks the
three. The checker before the change passes the trace (CONTRACT OK, the
faults reported only); faults.sh run with that checker gives `fillmb:
WRONG, expected FAIL` and FAULTS FAILED: 1, with the changed one FAULTS
OK. The fault `kindh0` (h set to 0) now fails S as well (157 BalancedOK
faults, which the checker reported before); its checks, KIND and no
other clause of the contract, are unchanged, and its comment and the
header say so.

`lean/contract/statements.pin`: ContractCheck.lean's line only. The
texts: ContractCheck.lean's header, faults.sh's header, and 030-26,
section 2.1 (the fill rules checked by both checkers) with a log line.
030-38 is unchanged.

Every run of the contract checker now fails on a shape fault: level2.sh's
step 8b, contractconf.sh (night.sh's contract-medium and contract-day)
and apptraces.sh. `java/night.sh` of 2026-11-23 had 0 shape faults on
every set, and the gates below 0 on the small and drain sets.


Gates
-----

On the branch `028-44` at d4cbb95b (no Java change):

* `lean/contract/faults.sh`: FAULTS OK (`fillmb: fails`);
  `faults-top.sh`: FAULTS OK; `bridge-faults.sh`: BRIDGE FAULTS OK.
* `lean/contract/check.sh small drain`: CONTRACT OK; tree-small 70
  traces, tree-drain 110, each `failures: C1 0, C2 0, C3 0, R1 0, L1 0,
  C4 0, C5 0 (... SKIPT), L2 0 (... LIVE 0), KIND 0; shape faults 0 []`,
  and the bridge with 0 failures (32 s).
* `lean/contract/pin.sh`: 144 files pinned; `lean/contract/gate.sh
  a87b8758`: GATE OK (254 theorems, the standard axioms only; no file
  changed outside its paths; pinned files changed:
  `lean/contract/ContractCheck.lean`).
* `java/stress/level2.sh`: LEVEL 2 OK (17 minutes at nice 10, under a
  load of about 20); step 0 `144 files have their pinned hashes`, step
  8b's contract lines as check.sh's above.


Log
---

2026-11-24. Registered by an agent of lead-1124, from 030-39, F6
(Frans, 2026-11-24, 006-33, point 3).

2026-11-24. Taken by an agent of lead-1124, on the branch `028-44`.

2026-11-24. Done by the same agent: the contract checker fails a trace
with a shape fault, kept out of the comparison with `checkVerdict`;
faults.sh's fault `fillmb`; d4cbb95b on the branch `028-44`.
