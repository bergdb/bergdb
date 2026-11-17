# 030-05. The contract spike: report

Created 2026-11-17 by Frans Lundberg. Status: open.

The report of the spike of 030-04, section 7: the writer's contract for
BergDB's key tree, the theorem on gets and scans, the contract checked on
Java's traces. Written by the spike's agent (Fable at high, started by
coord-1117 at 11:30). Not finished: see State.


# State

2026-11-17, 12:05. For an agent that continues.

- Branch `030-04-spike` in the clone
  `/Users/f/fl/bench/2026-11-17/spike/clone`; the package is
  `lean/contract/` (Lean v4.34.1, Mathlib v4.34.1; `lake exe cache get`,
  then `lake build`).
- Done: the tree, the readers, the invariants and the contract
  (`Contract/Tree.lean`, `Read.lean`, `Statement.lean`); the checker
  (`ContractCheck.lean`, `check.sh`) passes on all 180 traces of the level
  2 sets, 21,000 transactions; the frame's computation proved to give the
  frame (`Check.lean`); earlier times from the frame (`Proof/Frame.lean`);
  a get is right (`Proof/Get.lean`); the top theorems (`Theorems.lean`).
- Open, as `sorry`: the node's search lemmas (`Proof/Node.lean`) and
  `scan_contents` (`Proof/Scan.lean`).
- Next: `Proof/Node.lean`, then `Proof/Scan.lean`, then the example
  (one transaction from the empty tree), the gate of 030-04, section 7.6,
  and this report.
