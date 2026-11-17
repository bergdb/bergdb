# 030-05. The contract spike: report

Created 2026-11-17 by Frans Lundberg. Status: done.

The report of the spike of 030-04, section 7: the writer's contract for
BergDB's key tree, the theorem on gets and scans proved from it, and the
contract checked on Java's traces. Written by the spike's agent (Fable
at high, started by coord-1117 at 11:30 on Frans's word), "I" below.
All of it is on the branch `030-04-spike`; nothing is on `main`.


# 1. The result

**Success, by 030-04, section 7.5.** Both conditions are met.

- **(b) Proved.** For any history of transactions that each meet the
  writer's contract, from an empty tree, at every time, the latest and
  every earlier one: the tree meets the invariants (`inv_right`), every
  get gives what a plain map gives (`get_right`), and every scan gives
  what a scan of the plain map gives, forward and backward, with and
  without a start key and an end key, with a limit (`scan_right`). No
  premise is left but the contract. `#print axioms` shows Lean's three
  standard axioms only. An example, the empty tree and one put, meets
  the premises (`Contract/Example.lean`), so the theorems are not
  vacuous.
- **(d) Passing.** The contract holds for every traced transaction of
  the level 2 sets: 180 traces, 21,000 transactions, 291,691
  operations. Java's 84,000 GET lines and 21,000 SCAN lines are what the
  package's readers give. No failure. Beyond the brief, with no
  failure either: the reclaim set (15 traces, 8,735 transactions,
  reclaim's own records among them) and 16 of the 27 traces of the
  medium set (6,760 transactions, 362,026 operations). I stopped the
  medium run there: `treeconf.sh`'s old checker needs long for the
  traces of node size 62.
- **The gate of section 7.6 passes:** `lean/contract/gate.sh 66db6126`
  prints GATE OK.
- **Lines, hours, share.** 4,890 lines of Lean: 867 to read and trust,
  3,434 of proof, 486 of the checker, the rest the example and the
  gate. About an hour and a half, 11:31 to 12:56. About 4 % of the
  week: 20 % at the start, 24 % at the end, by the coordinator's watch.

Proved means a Lean theorem with no premise left open. What is proved
speaks of histories that meet the contract. That Java's writer, or the
model's, meets the contract is tested, not proved.


# 2. What there is

`lean/contract/`, a Lake project of its own (Lean v4.34.1, Mathlib
v4.34.1).

- **To read and trust:** `Contract/Tree.lean` (a tree as Java has it:
  key nodes as klongs, the live klongs, the five searches), `Read.lean`
  (`get`, `scan`), `Statement.lean` (the invariants, the contents, the
  plain map and the contract, in English and in Lean: deliverable (a)),
  `Theorems.lean` (the three theorems).
- **The proofs:** `Contract/Proof/`, eight files.
- **The check:** `Contract/Check.lean`, `Shape.lean`, `Trace.lean`,
  `ContractCheck.lean`, and `check.sh`, which runs it on the traces.


# 3. The contract, as settled

A transaction with operations `ops` runs at time i on the tree s and
ends in the tree s' with the dirty nodes D (`Contract`):

1. s' at time i meets the invariants (`invOk`).
2. The contents of s' at time i are the contents of s at time i - 1
   with the operations applied in a plain map.
3. The frame: every node of s is a node of s'; a value is unchanged; a
   key node keeps its level, its kind and its klongs, and klongs are
   added only after a time klong of time i; a node not in D is
   unchanged; a key node made is in D; space roots are only added, with
   time i.

The points of 030-04, section 3.2:

- **The fill rule is not in the contract** (deliverable (c)): no reader
  needs it. Of the invariants, the proofs use only the rules of a
  node's bitmaps (W2 to W4), the kinds of the nodes, the key order and
  "a live klong in every node". The last is needed for two things: the
  reader's fuel is enough, and a forward scan may stop at its end key.
  The fill, the two live klongs of an inner root, the leftmost rule
  (LE-b), the bound on dead klongs and the balance are the writer's own
  rules: computed apart (`shapeFaults`) and tested, with no fault in
  the 21,000 transactions. A caution for 030-04, section 3.6: a proof
  that the writer meets the contract will want the fill and the root
  rule as premises of its own, since a merge relies on a sibling.
- **Earlier times are in clause 3,** as 030-04 guessed. A reader at
  time t reads each node up to its first time klong after t, so after
  a transaction that meets the frame it sees what it saw
  (`Frame.earlier`).
- **The contents are read off the tree alone:** from a key node, its
  live klongs in order; no search is used. Java's five searches are
  proved to be lookups in the live klongs.
- **Accepted transactions:** a history has only the transactions that
  ran; a refused one is no step.


# 4. The check, and its gaps

`lake exe contractcheck` checks each traced transaction alone, on
Java's tree before and after it: the invariants, the contents, the
frame, and Java's GET and SCAN lines against the readers.

- **It is the contract of (a).** Clauses 1 and 2 are the same
  definitions. Clause 3 is computed over the nodes of a hash map, and
  `frameCheck_sound` proves that the computation gives the frame; so
  what the checker computes is `Contract` (`checkTx_sound`).
- **It can fail.** Six hand-made faults in a trace (an operation
  dropped, a pointer changed, a wrong GET answer, a wrong time klong, no
  GD lines, a wrong compare value) were each found.
- **Gaps left.** How the checker builds Java's tree from a trace's
  lines is not proved (`applyTx`: NEW, KN, ADD, GD and DIRTY lines). The
  top is its specification, the space root from each time on, without
  the top nodes and the search through the skip pointers (as 024-12,
  D6). Values are their hashes, keys their compare values.


# 5. Findings

1. **D is the dirty set when the transaction ends, before its record is
   written:** D after the record before, and the nodes that got dirty.
   My first check took the GD line alone, and the frame failed for 188
   of 300 transactions: a node that is dirty already gets klongs without
   getting dirty again. By 030-04's rule I suspected the contract first,
   and it was my reading of D. No fault of Java.
2. **No statement turned out false.** The scan's theorem asks for a
   start key and an end key as `Keys.toSegments` makes them, as TP11
   did; the get's holds for every key. Java's -1 and `Long.MAX_VALUE`
   are modelled as below and above every compare value, so no bound on
   compare values is needed.
3. **The scan's proof is one idea:** for a chain that is a path, the
   contents are what is before the chain, at it and after it
   (`Path.split`); `next` gives the first key after the chain, and the
   setup puts the chain at the start key.


# 6. Mathlib, and what was copied

- **Cost:** 7.6 GB in `.lake/packages`; the first setup took 5 minutes;
  a build of the package from nothing takes 26 seconds.
- **Gave:** the order of lists (keys), `WithBot` and `WithTop` for the
  scan's positions, and tactics. Most list lemmas used are Lean's own.
- **Little of it is used.** It could be dropped for about 200 lines of
  order lemmas. I kept it: step 4 (maps, sets of nodes) is likelier to
  use it. The definitions that run import only Lean's `Std`.
- **Copied from the old Lean, as definitions, adapted:** from
  `SIS/Tree/Node.lean`: `Klong`, `lastBitmap`, `prefixAt`, `segLen`, the
  searches; from `Read.lean`: the scan and the get. The walk and
  `klongsWf` follow `Inv.lean`'s ideas, rewritten. No proof was copied
  or read.


# 7. What is next

- **Step 4, the abstract model: reuse it.** By reading its assumptions
  (`lean/SIS/Assumptions.lean`), not by building. Its theorems take
  each transaction's change as given, so a transaction can be its own
  change. To make:
  - the contract's tree as the model's structure: klongs as entries
    (the old D3 and D4), and the top nodes with their skip pointers;
  - more clauses in the contract, the fields of `StepOK` and of the
    eviction assumptions that reads did not need: what a transaction
    makes or changes is reachable at its time (A2, A3), every pointer
    goes to a lower level (A4), no resurrection (A5), the top's rules
    (R1 to R4), the touch, TREE, A6', A-COPY. `tracecheck` tests them on
    the traces today.
- **Also:** `check.sh` as a step of `level2.sh` (Lake fetches Mathlib to
  resolve the package even for the checker alone); Java's own check of
  the invariants in its tests; 030-04's list of section 3.5 with the
  test beside each assumption.


# State

2026-11-17, 12:56. GATED, by 030-04, section 7.6.

- Branch `030-04-spike` in the clone
  `/Users/f/fl/bench/2026-11-17/spike/clone`, from `main` 66db6126.
- To build: `cd lean/contract`, `lake exe cache get`, `lake build`. To
  check the traces: `java/build.sh`; `cd lean && lake build treecheck`;
  `java/stress/treeconf.sh small` and `drain`; `lean/contract/check.sh`.
  The gate: `lean/contract/gate.sh 66db6126`.
- Nothing is open in the spike. What comes after it is section 7.


# Log

2026-11-17, 11:31 to 12:56. The spike, one agent (Fable at high).
11:53 the definitions and the checker, passing on the traces; 12:11 the
get proved; 12:35 the scan proved; 12:40 the example and the gate.
