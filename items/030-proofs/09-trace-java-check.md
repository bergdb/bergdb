# 030-09. The trace's completeness and Java's own check of the contract

Created 2026-11-17 by Frans Lundberg. Status: open.

Step 4c of 030-04, the night of 17 to 18 November: the tested half of the
contract approach made solid. Every traced transaction is checked
completely (030-06, findings 1, 2 and 7), the assumptions that reads rest on
are named with their tests (finding 6), and Java checks the contract itself
in its tests. Written by an agent of coord-1117 ("I" below), on the branch
`030-09-java-check`.


# 1. The result

- **A trace is checked whole** (F1, F2, F7). `contractcheck` reads a trace
  only if it is whole: `TRACE 3`; no `ERROR` line and no line of an unknown
  kind; the transactions numbered 0, 1, 2, ... each from `TX i` to `END i`;
  the last line `DONE n` naming the last; in each transaction a `NEW` line
  only for a node not made before, every `ADD` line at the transaction's
  time, a `KN` line for every key node made, a `V` entry for every value
  made, a root pointer for every top node made, the root's entry only for a
  top node made, one `GD` and one `DIRTY` line
  (`lean/contract/Contract/Complete.lean`). A KN line must hold exactly its
  klongs, a SCAN line exactly its results, an OP line is P, D or N.
- **The exporter writes a KN line from a klong diff** (F1):
  `TraceExport` writes a KN line for every key node whose klongs the
  transaction changed in any way, not only for those it gave an entry. A
  klong changed or removed is then both an ERROR line and a KN line, which
  the frame (C3) fails. On the level 2 sets the KN lines are the same as
  before (48,239 on the small set), so Java changes no klong of an old node.
- **Proved: a traced history is a history** (F2). `historyOk_meets`
  (`Contract/History.lean`): from a start heap that passes the start check,
  transactions at times 1, 2, ..., each passing `checkTx`, give `Meets`.
  The checker checks TX j at time j and fails unless the trace numbers it
  j, so the theorems on reads hold for the traced tree at every time of a
  trace that passes. Standard axioms only.
- **LIVE lines checked** (F6, the readers): with `live=1`, every LIVE line is
  Java's `searchEq` of each compare value of each node at each of its
  times, and Java's top search at every time (record times and the times
  between them), compared with the package (L1). `hot` and `d-random` of the
  tree sets now run with `live=1`: 2,729,666 LIVE lines on the small and
  drain sets, none differ.
- **The checker's own test**, `lean/contract/faults.sh` (about a second;
  `check.sh` runs it first): 14 faults made by hand in a good trace, and one made in
  Java (`TraceExport`'s new `fault=I`: a klong of an old node changed in
  memory), each make the checker fail; the Java fault fails with its ERROR
  line and, with the ERROR line taken out, by the frame alone.
- **The level 2 sets pass:** `treeconf.sh small` and `drain` TREECONF OK;
  `check.sh small drain` CONTRACT OK, 180 traces, 21,000 transactions,
  291,691 operations, 84,000 GET, 21,000 SCAN, 2,729,666 LIVE, no failure.
- **The assumptions reads rest on** beyond 030-04's five (F6): written into
  030-04, section 3.5, as items 6 to 9, each with its test.
- **Java's commit-time check:** in progress (section 3).


# 2. Decisions

- **The completeness check is a pass of its own over the lines**
  (`Complete.lean`), not a change of `readLine`. Reason: three agents share
  `Trace.lean` and `ContractCheck.lean` tonight; my hunks there are small
  (a `lives` field and its line, strict klong and result counts, OP D or N,
  the call of `completeFault`, the TX number and the LIVE check in the
  loop).
- **Every ERROR line fails, wherever it stands.** The exporter writes them
  at the head of the trace; any one is a change that the trace cannot
  express (027-02, section 2).
- **PROBE lines do not fail the contract's checker.** They are run B's;
  `tracecheck` checks them. The contract is checked on run A.
- **F7, node permanence and levels, by the trace's meaning, not by a
  test:** the heap only grows because the stream does (a node of the trace
  is a node written or in D, and nothing is removed from an append-only
  stream); a level is the trace's number for a node, computed from the
  final structure (027-02, section 2), so "keeps its level" holds by
  construction and Java has no level to change. The third part of F7, the
  roots' times, is now tested: every ADD line, the root's entries too, must
  be at the transaction's time.
- **The KN diff compares the KN line's text** (klongs and pointee ids), so a
  pointer of an old klong that comes to name another node shows too.
- **`gate.sh` allows `java/` and 027-02** (step 4), with a note that
  `java/before-commit.sh` must print BEFORE COMMIT OK. Reason: this item's
  brief changes the exporter and the trace format with the checker.
- **`historyOk_meets` is a theorem about the checker's definitions**, not
  about its loop: the loop computes the same `checkTx` at time j for TX j
  (it fails otherwise) and the start check for TX 0; the loop itself is a
  program, as before (030-06, section 8).


# 3. Java's commit-time check

In progress.


# 4. Tests run

- `lean/contract/gate.sh fc183148`: GATE OK (8 theorems, standard axioms).
- `java/before-commit.sh`: BEFORE COMMIT OK (67 s).
- `java/stress/treeconf.sh small` and `drain`: TREECONF OK.
- `lean/contract/check.sh small drain`: CONTRACT OK (36 s, with faults.sh).
- `lean/contract/faults.sh`: FAULTS OK.


# State

2026-11-17, 16:10. Items 1 to 4 of the brief done and gated; item 5 (Java's
commit-time check) next, then item 6 (the medium set).

- Branch `030-09-java-check` in `/Users/f/fl/bench/2026-11-17/night/s4c/clone`.
- To build: `java/build.sh`; `cd lean/contract && lake build`. The traces:
  `java/stress/treeconf.sh small` and `drain` (needs `cd lean && lake build
  treecheck`). The check: `lean/contract/check.sh small drain`. The gate:
  `lean/contract/gate.sh fc183148`.


# Log

2026-11-17, 15:09 to 16:10. Read the brief, 030-04 to 030-06 and the
package; the completeness pass, `historyOk_meets`, the LIVE check, the
exporter's klong diff and fault, faults.sh; the level 2 sets rerun.
GATED e58d56f8: the trace's completeness (F1, F2, F7), KN from a klong diff, LIVE lines
checked, `historyOk_meets`, faults.sh, 030-04 3.5 items 6 to 9 (F6); BEFORE COMMIT OK,
level 2 sets TREECONF OK and CONTRACT OK.
