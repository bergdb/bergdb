# 030-09. The trace's completeness and Java's own check of the contract

Created 2026-11-17 by Frans Lundberg. Status: done.

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
- **Java checks the contract itself, in its tests** (section 3):
  `TransCheck`, off by default, on with `transcheck=1`. After each
  transaction's puts it checks, on the nodes the transaction made, changed
  or replaced and on their neighbours, the invariants, the contents of the
  transaction's keys and of the leaves it touched, the frame and D, and
  Java's search. On in the unit tests (`before-commit.sh`, `unit.sh`; no
  cost seen); the f-tests with it are `java/stress/transcheck.sh`, a step
  of `night.sh`, since there it costs about 7 s. No failure in 4.3 million
  transactions of the unit tests and f-tests, with restarts, eviction,
  reclaim and the Pub layer; `TransCheckTester` shows that it finds four
  kinds of fault made on purpose.
- **The medium set, contract check only** (030-05 stopped at 16 of 27):
  all 27 traces CONTRACT OK, 13,667 transactions, 736,718 operations,
  109,336 GET, 27,334 SCAN, node sizes 8 to 62; no trace not whole, no
  ERROR line. 51 s to export, 319 s to check, four at a time (section 4).


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

`java/src/bergdb/core/TransCheck.java`, test-only: on with the system
property `transcheck=1`, off by default, so production runs none of it
(Db holds a `TransCheck` only when the property is set; the cost when off
is a null test per node change). `before-commit.sh` and `unit.sh` turn it
on in the unit tests; the f-tests run with it in a script of their own,
`java/stress/transcheck.sh`, a step of `night.sh` (measured below). Db calls it at the start and the end of each
transaction's puts (`Db.putKvs`), under the write lock, and tells it the
key nodes the transaction made, changed, replaced and took back (Db's
`Dag.NodeChangeListener`). It reads no stream: a pointer to a node not in
memory ends the check there.

Two walks from the space root through the live klongs, at the
transaction's time tt and at tt - 1, visit the nodes on the paths of the
transaction's keys and every node made, changed or replaced that they reach
from such a node. On them, the clauses that can be checked locally:

- **Clause 1:** at most M klongs; W1 to W4; a pointer for every key klong;
  a live klong (but in a space root that is a segment leaf); the key order
  with the ranges passed down; on every live child, in memory, of a node
  made or changed, its kind (key node or value), a live klong, and the key
  order in it. No node is reached twice (TREE, beyond the contract).
- **Clause 2:** each key of the transaction has its new value at tt, or
  none if deleted; every other key of a segment leaf made, changed or
  replaced has the same value at tt - 1 and at tt (its keys at tt - 1 are
  found at tt, and its keys at tt were there at tt - 1).
- **Clause 3:** a node the check has seen after an earlier transaction
  keeps its klongs (a hash of them and their number), and the klongs added
  start with a time klong of tt; a node replaced has none added; a node
  made or changed is dirty (in D) unless replaced or taken back. Beyond the
  contract (030-06, finding 4): every time klong of a node made is of tt.
- **The search:** in each node made or changed, `KeyNode.searchEq` of each
  live compare value finds the klong that the contract's live klongs name.

Not local, so not checked in Java: a node not in D is unchanged, the key
order and kinds beyond the nodes visited, the levels, the contents beyond
the leaves touched. The traces check them. The walks keep no Java stack
(keys of thousands of segments; `DbTesterLongKeys` runs the writer with a
256 kB stack, which a first, recursive version overflowed).

`TransCheckTester` makes four faults in the space root during a
transaction, through `Db.TestHooks.kvApplied`: a klong of an old node
changed, its last klong removed, a klong added without the time klong, and
a bitmap at tt that deletes a key the transaction does not touch. The
check finds each (the frame three times, the contents once).

Where it runs: in every Db of the unit tests and the f-tests, so with
restarts, eviction, reclaim's internal transactions, the Pub layer's
objects and indexes, and threads; not in the startup's rerun, which puts
through the Dag, not `putKvs`. This is what ties assumption 9 of 030-04,
3.5 to runs other than the traces' run A.

**What it checked, one run of each** (no failure): the unit tests 130,517
transactions, 1,591,928 nodes visited, 385,895 made, 562,624 keys of the
transactions, 2,559,611 reads; the f-tests 3,833,784 transactions,
11,884,861 nodes visited, 760,395 made, 4,464,540 keys, 28,606,929 reads.
No node made or changed was left unreached by the walks.

**The cost, measured on F53 (load 6 to 9, other sessions busy):** the unit
tests 39.2 and 38.0 s with the check, 49.4 (load 21) and 39.2 s without:
no cost seen. The f-tests alone, twice each: 49.9 and 49.8 s without, 57.4
and 56.7 s with: about 7 s more. Side by side, as `before-commit.sh` runs
them, the f-tests set the wall time (54 to 59 s without, 62 to 63 s with).
**Decision:** by the brief's rule (more than a few seconds goes to a script
of its own), `before-commit.sh` turns the check on in the unit tests only,
which end 15 to 20 s before the f-tests, so its time is unchanged; the
f-tests with the check are `java/stress/transcheck.sh` (about a minute),
step 2b of `night.sh`.


# 4. Tests run

- `lean/contract/gate.sh fc183148`: GATE OK (8 theorems, standard axioms).
- `java/before-commit.sh`: BEFORE COMMIT OK (67 s).
- `java/stress/treeconf.sh small` and `drain`: TREECONF OK.
- `lean/contract/check.sh small drain`: CONTRACT OK (36 s, with faults.sh).
- `lean/contract/faults.sh`: FAULTS OK (also after 030-08's merge, with C4).
- Java's check: `java/stress/transcheck.sh` TRANSCHECK OK (unit and f-tests
  with the check, 66 s); `before-commit.sh` with it in the unit tests:
  BEFORE COMMIT OK (63 s); `TransCheckTester`: 4 faults found.
- The medium set: `TraceExport` with `tree=1` on `treeconf.sh medium`'s 9
  configurations, seeds 1 to 3, then `contractcheck` on each trace (no
  `treecheck`): 27 of 27 CONTRACT OK, C1 to C4, R1 no failure. The script
  is in my scratch (`/Users/f/fl/bench/2026-11-17/night/s4c/medium.sh`):
  the medium function's lines of `treeconf.sh`, each config with
  `-Dtree=1` and seeds 1 to 3, then `lean/contract/.lake/build/bin/contractcheck`.


# State

2026-11-17, 15:57. The brief's six items are done; the last gated commit is
2c8a9da3 (gate base 9a6692cf). Nothing is open here. What could follow:
the f-tests' check in `before-commit.sh` if its 7 s are made smaller (the
walk at tt - 1 and the reads of the leaves' keys are most of it, by
reading the code, not measured); the check in the startup's rerun
(DbStarter puts through the Dag, not `Db.putKvs`); `live=1` in more tree
configurations.

- Branch `030-09-java-check` in `/Users/f/fl/bench/2026-11-17/night/s4c/clone`.
- Java's check: `java/stress/transcheck.sh`; `java/unit.sh -c TransCheckTester`.
- To build: `java/build.sh`; `cd lean/contract && lake build`. The traces:
  `java/stress/treeconf.sh small` and `drain` (needs `cd lean && lake build
  treecheck`). The check: `lean/contract/check.sh small drain`. The gate:
  `lean/contract/gate.sh fc183148`.


# Log

2026-11-17, 15:09 to 15:27. Read the brief, 030-04 to 030-06 and the
package; the completeness pass, `historyOk_meets`, the LIVE check, the
exporter's klong diff and fault, faults.sh; the level 2 sets rerun.
GATED e58d56f8: the trace's completeness (F1, F2, F7), KN from a klong diff, LIVE lines
checked, `historyOk_meets`, faults.sh, 030-04 3.5 items 6 to 9 (F6); BEFORE COMMIT OK,
level 2 sets TREECONF OK and CONTRACT OK.
GATED 2c8a9da3: Java's own check of the contract in its tests (TransCheck, off by default;
on in the unit tests, the f-tests in stress/transcheck.sh, a night.sh step), TransCheckTester;
BEFORE COMMIT OK (63 s), TRANSCHECK OK; gate base 9a6692cf.
2026-11-17, 15:27 to 15:57. Pulled main 9a6692cf (030-08's C4), faults.sh
still passes; TransCheck and its tester, measured, transcheck.sh; the
medium set, contract check only, 27 of 27.
