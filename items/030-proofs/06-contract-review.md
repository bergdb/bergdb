# 030-06. An independent review of the writer's contract

Created 2026-11-17 by Frans Lundberg. Status: done.

A review, with fresh eyes, of the spike 030-05: the writer's contract of
030-04 in `lean/contract/`, the theorems proved from it, and its trace
checker. Written by a review agent of coord-1117 from the coordinator's
brief of seven questions. No statement is changed. Two Lean examples are
added (`Contract/Example3.lean`, `Contract/ExampleDag.lean`), with their
lines in `Contract.lean` and `Axioms.lean`.


# 1. The result

**Sound, with fixes.** The theorems are proved (the gate passes, Lean's
three standard axioms only) and not vacuous (a history of three
transactions builds). The contract says what 030-04 means for gets and
scans, with no circularity and earlier times right. Java met it on every
trace I ran: 120 traces, 20,154 transactions, 231,087 operations, node
sizes 8 to 62, keys of up to 5 segments, the reclaim set; no failure, no
ERROR line. The checker is the contract (`checkTx_sound`, no gap). The
weak points are around them: what the checker reads from a trace, and
what the contract leaves to step 4.

1. **Must fix before step 4: an ERROR line passes.** If Java changes or
   removes klongs of an existing node (what clause 3 forbids), the
   exporter writes ERROR and no ADD or KN line for the node
   (`TraceExport.java`:674-678, 922); the checker drops ERROR lines
   (`Trace.lean`:146), keeps the old node and passes. A trace with an
   ERROR line added prints CONTRACT OK. Fix: ERROR and unknown lines in a
   TX fail; the exporter writes KN for every key node whose klongs changed.
2. **Must fix before step 4: the trace is not checked to be a history.**
   `Meets` needs transaction j at time j; the checker takes TX numbers as
   they come (`ContractCheck.lean`:52) and passes a cut trace (:96). A
   trace without its TX 20 (an empty one), and one cut after TX 29, pass.
   Fix: TX numbers 0, 1, 2, ..., and a DONE line naming the last.
3. **Must, in step 4: the abstract model's assumptions are not in the
   contract** (section 4): TREE, A2, A3, A4 for dead klongs, A5, the top
   (R1 to R4), the touch, A6', A-COPY. Shown for TREE in Lean:
   `ExampleDag.lean` meets the contract with a node that is the live
   child of two reachable nodes. Fix: clauses 4 and up; `tracecheck`
   tests most of them on traces today.
4. **Should fix: klongs added at time i may carry later times.** `Ext`
   (`Statement.lean`:333) and `extKs` leave `more` free. Reads stay right
   (proved), but the abstract model's change is entries at time i, and
   the exporter calls this an error (`TraceExport.java`:685). Fix: no
   time klong in `more`; a new key node's klongs all at time i.
5. **Should fix: D is free.** `Meets.step` takes any D
   (`Statement.lean`:357); no proof uses clause 3's D part; D = all nodes
   meets it. Fix: say so; in step 4 make D state, or leave it to the
   abstract model.
6. **Should fix: Java's reads need more than 030-04's five assumptions.**
   Also: Java's searches, scan and top search are the Lean readers
   (tested by GET and SCAN lines; the top search by LIVE lines, section
   7: 333,674 lines, none differ); the OP lines are the user's
   transaction (`Db.putKvs`; not tested by the checker); a refused
   transaction changes nothing; the contract is checked on run A only (no
   eviction, no restart). Fix: name them in 030-04, 3.5, each with its test.
7. **Note: part of the frame cannot fail in the checker.** `applyTx`
   (`Trace.lean`:160-173) never removes a node, copies levels, and stamps
   new roots with the TX number. Levels are computed after the run
   (027-02), so a Java check at commit needs a level of its own.
8. **Note: the gate does not pin the statements** (030-04, 4.2). Fix: a
   step 5 in `gate.sh`, `git diff --quiet BASE` on the four trusted files.

The two simplifications (section 7): the top is a reader assumption, cheap
to test exhaustively now and to prove with step 4's top clauses (TP24, 400
to 1,000 lines); `applyTx`'s risk is the trace's completeness (findings 1,
2, 7), closed by tests, about 30 lines of Lean and 20 of Java test code.


# 2. What the contract demands, in plain words

A transaction runs at time i on the tree s, with the operations `ops`,
and ends in s' with the dirty nodes D (`Statement.lean`, section 5).

- **Clause 1** (`invOk p (s'.at i)`). The tree that a reader at time i
  sees is sound. There is a space root, a key node. Every node reached
  from it through live klongs has at most M klongs; its klongs start with
  a time klong, times increase, and each bitmap deletes only key klongs
  before it, holds the bitmap before it, and deletes every earlier klong
  of a compare value it deletes; each of its key klongs, live or dead,
  names a node that exists. A live klong of an inner node names a key
  node of a lower level; of a segment leaf, a value for a short segment
  and a non-empty key node of a lower level for a long one. Every node
  reached has a live klong (a leaf space root may not), and the compare
  values keep the key order, by ranges passed down.
- **Clause 2.** The contents of s' at i are the contents of s at i - 1
  with `ops` applied in order to a plain sorted map. The contents are
  read off the tree by the walk through live klongs; no search is used.
  The operations are the Dag's (the OP lines, `Db.putKvs`), not the
  user's transaction as built.
- **Clause 3.** No node of s goes away or changes kind. A value is
  unchanged. A key node keeps its level, its kind and every klong; it may
  get klongs at the end, the first of them the time klong of i. A node
  not in D is unchanged; a new key node is in D. The list of space roots
  only grows; the roots added have the time i.

**No circularity.** `contents` (`Statement.lean`:207-220) uses `live`
and the walk. The readers use Java's five searches (`Tree.lean`,
`Read.lean`), which the proofs show to be lookups in `live`
(`get_contents`, `scan_contents`). `live` is the meaning of a node,
shared by both; it is not a reader.

**Earlier times: right.** A reader at t < i cuts each node before its
first time klong after t (`prefixAt`) and takes the last root at or
before t. Clause 3 makes s' cut at t hold s cut at t (`Frame.sub`), so
the invariants and the contents at t carry over (`Frame.earlier`). A new
node is not reached at t, since every pointer reached at t names a node
of s (PointersOK). Every time 0 to n is a transaction's, so "the last
transaction at or before t" is transaction t. Java's clock times between
records are mapped to t by the exporter, outside the contract.


# 3. Too weak?

For reads, no: a writer that meets the contract at every step gives
right gets and scans at every time of its history; that is proved. A
user-visible fault must come from outside the contract, from the
assumptions of finding 6:

- **The readers.** The theorems speak of the Lean readers. That Java's
  `getOne`, `getMany` and `findSuperRootAtTime` are these readers is
  tested: each GET and SCAN line of a trace (four GET and one SCAN a
  transaction, at random times), and the top search by the LIVE lines of
  section 7.
- **The operations.** Clause 2 compares the tree with the OP lines,
  which the exporter takes from `Db.putKvs` (`Db.java`:3382, the
  `kvApplied` hook). A fault in the step from the user's transaction to
  the Dag's operations, or in `Keys.toSegments`, passes the contract and
  the GET lines alike, since both read Java's tree. Run B's lookups
  against the workload (`probe=1`) and Java's unit tests cover it; the
  tree sets run with `probe=0`.
- **Refused transactions.** 030-04, 3.2 says that a refused transaction
  changes nothing; the contract makes it no step, so a refused
  transaction that left klongs behind is neither stated nor tested here.
- **Run A only.** The KN lines are run A's, a writer that never restarts
  or evicts. Java's writer after a restart or with eviction is tied to
  run A by the stream comparisons of runs B and E (level 4), not by the
  contract.

For step 4 the contract is too weak, as 030-05, section 7 says: the
clauses of section 4 are missing. One of them shown in Lean:

    -- Contract/ExampleDag.lean: one transaction from the empty tree puts
    -- [56, 8] and [120, 8]; leaves 5 and 6 share node 3.
    theorem meets : Meets p [ops] s1 := ...
    example : s1.root = some 4 ∧ (live inner.ks).map (·.2) = [5, 6] ∧
        (live leaf5.ks).map (·.2) = [3] ∧
        (live leaf6.ks).map (·.2) = [3] := by decide

Within one segment tree, the ranges and the non-empty leaves rule
sharing out; across segments, nothing does.


# 4. The clauses step 4 needs

What the abstract model assumes (`lean/SIS/Assumptions.lean`, `StepOK`
and `VirtStep`; `lean/SIS/Phys.lean`, `treeAt`, `adoptAt`, `CopyStep`;
006-26, sections 2.1 and 5.2) and the contract does not give:

- **The klongs as entries.** The map from a key node's klongs to the
  model's entries (a bitmap as the compare values it deletes, the times
  from the time klongs), so that a contract step is a `Changes`.
- **Entries at time i** (finding 4): the klongs that T(i) adds or makes
  are all at time i.
- **A2** (`current`): klongs are added only to nodes reachable at i. The
  contract lets a writer extend an unreachable node of D.
- **A3** (`newReachable`): every node made, values too, is reachable at
  i. The contract allows nodes made and dropped.
- **A4** (`levels`): every pointer, of dead klongs too, goes to a lower
  level. The contract asks it of live klongs only.
- **A5** (`noRes`): a node reachable at i was reachable at i - 1 or is
  new. The contract allows a writer to link an old subtree again.
- **TREE** (`treeAt`): every reachable node but the root is the live
  child of exactly one reachable node. Not implied (section 3).
- **The top** (`VirtStep`, R1 to R4 and `dead`): top nodes with their
  root and skip pointers in the contract's tree; at most one new top node
  a transaction, the root's entry for it, a top node fixed after its
  transaction, the skip pointers reach every older top node, and a skip
  target is not reachable. The contract's roots allow several new roots
  at time i (the last one wins).
- **The touch** (`touchIndex`, `touchReach`, `touchUp`): reclaim's
  touched nodes, from the TOUCH line, with their rules.
- **A6'** (`adoptAt`) and **A-COPY** (`CopyStep`): what a dead pointer of
  a reachable node and the pointer of a new klong may name.
- **D** (finding 5): Java's D as the model's D, or none.
- **Later, not step 4:** bounded startup needs the heights (006-26,
  5.3, H); the contract left the balance out with the fill.

`tracecheck` tests all but the klong map on Java's traces today (006-26,
section 2.4), so each clause has a test before it is written.


# 5. Too strong?

I found no clause that Java fails. The runs, with the clone's
`TraceExport` (`tree=1`, the configurations of `java/stress/treeconf.sh`)
and the package's `contractcheck`:

- small, 7 configurations, 10 seeds: 70 traces, 7,100 transactions;
- drain, 9 configurations, 4 seeds: 36 traces, 4,360 transactions;
- reclaim, 4 configurations, 2 seeds: 8 traces, 4,960 transactions,
  reclaim's steps and table records among them;
- medium m-d62 (node size 62, 79,031 operations), m-long, m-r-del: 3
  traces, 1,934 transactions;
- large l-big62 (node size 62): 1,000 transactions;
- hot and m-mixed with `live=1`: 2 traces, 800 transactions.

No C1, C2, C3 or R1 failure, no shape fault, no ERROR line. The traces
reached keys of 5 segments, trees of height 6 in a segment, and 130 top
nodes. Not reached: node sizes above 62, more than a few hundred top
nodes, deep trees of large databases, and Java under eviction or after a
restart (run A only, section 3). Three parts of the frame cannot fail in
the checker (finding 7), so on traces they test nothing.

The clauses most likely to meet a Java state not yet traced are W4 (a
bitmap deletes every earlier klong of its compare values) and NonEmptyOK
for the root of a next segment's tree; both held through the draining
and long-key sets. `bitsOf` reads 64 bits; Java writes 62
(`klong & 0x3fff...`), enough for node size 62.


# 6. Vacuity

Not vacuous.

- `Example.lean` meets every premise of the three theorems at once: one
  `Meets` gives the get at times 0 and 1 and the scan. It is thin: one
  leaf, one put, no inner node, no new root, no delete.
- `Example3.lean` (new; builds, standard axioms) is a history of three
  transactions: a put; a put that splits the root into a new inner root
  (a new space root at time 2); a delete that unlinks a leaf by a bitmap
  in the inner root, leaving a dead klong to a node no longer reached.
  The theorems then give reads at all four times, among them
  `get (s3.at 1) [8] = some 5` and `get (s3.at 3) [8] = none`.
- `ExampleDag.lean` (new) adds keys of two segments.
- The traces are executable witnesses: `checkTx` holds for histories of
  up to 1,034 transactions, and `checkTx_sound` makes each step a
  `Contract`. That rests on the compiled checker, not on the kernel.


# 7. The two simplifications

**The top: one root per time.** The checker's roots come from Java's own
top data (`ADD 0 i T z`, `ADD z i R y`), so the contract is about Java's
roots; what is assumed is Java's search, `findSuperRootAtTime` with its
skip pointers, which `TopDs` implements in about 100 lines with a cache
of times. Today only the GET and SCAN lines test it, at random times. It is
cheap to test at every time: with `live=1` the exporter writes Java's top
node at every time up to each record, at record times and between them
(LIVE 0 t z). An awk prototype of the check (the root pointer of z is
the contract's root at t) found 88,758 lines of `hot` (100 top nodes)
and 244,916 of `m-mixed` all equal. Closing it by test: the same check
in `contractcheck`, about 20 lines, and `live=1` in the tree sets. By
proof: top nodes in the contract's tree with the rule of
`TopDs.newSuperRoot` as a clause, and the search proved to give the last
root at or before t: TP24, which the old line stated and never proved
(`lean/SIS/Tree/Top.lean`), perhaps 400 to 1,000 lines. Step 4 needs top
nodes anyway for R1 to R4. Serious for the claim only as the readers are:
a tested assumption, now tested sparsely.

**`applyTx`: Java's tree from the trace lines.** Its 15 lines are not the
risk; a proof of them would say little, since Java is not in Lean. The
risk is that the lines are not all of Java's change: the KN lines come
from the exporter's entry diff and an ERROR skips them (finding 1); the
history may skip or end early (finding 2); levels, node permanence and
root times are put in by construction (finding 7). Closing it: the fixes
of findings 1 and 2 (about 30 lines of Lean), a KN line from a klong diff
in `TraceExport` (about 20 lines of test code), and a NEW line required
for every key node first seen in a KN line (now level 0,
`Trace.lean`:168). The old checkers tie the ADD lines to the stream's
versions (`tracecheck`) and the KN lines to the model's writer
(`treecheck`); `contractcheck` alone does not.


# 8. The checker and the contract

`checkTx` is `contractOk && frameCheck` (`Check.lean`:55-57).
`contractOk` is clauses 1 and 2 word for word, and `frameCheck_sound`
proves that the computed frame gives `Frame`; so `checkTx_sound` gives
`Contract` with no gap. The start is checked inline with the same
definitions as `Start`. The checker's own loop recomputes the parts and
compares them with `checkTx`. The gaps are outside the definition: TX
numbers and the end of a trace (finding 2), and what the heap is built
from (section 7).


# 9. The gate

Run in the clone, on 2590ce30 with the two examples:

- `lake build`: passes, no warning; 26 s from nothing in 030-05, 7 s
  here with the cache.
- `gate.sh 2590ce30`: GATE OK. `#print axioms`: `inv_right`,
  `get_right`, `scan_right` and `checkTx_sound` depend on `propext`,
  `Classical.choice` and `Quot.sound`; the three examples' `meets` on
  `propext` and `Quot.sound`.
- grep of the package (`.lake` aside): no `sorry`, `admit`,
  `native_decide`, `axiom`, `implemented_by`, `extern`, `opaque`,
  `unsafe`, `partial` or `set_option`. One instance, a `LinearOrder` on
  `Pos` in `Proof/Lex.lean`, used by proofs only; the statements compare
  with Bool functions (`Pos.above`, `Pos.below`). The examples use
  `decide`, checked by the kernel.
- The trusted files import only Lean's `Std` (`Statement.lean`,
  `Tree.lean`, `Read.lean`); `Theorems.lean` imports the proofs, which
  import Mathlib.
- Not checked by the gate: that the trusted files are those of the base
  (finding 8).


# 10. How this was checked

- Read: 030-04 (sections 1, 3, 7), 030-05, all of `lean/contract/`,
  `lean/SIS/Assumptions.lean`, the stage 2 assumptions of
  `lean/SIS/Phys.lean`, 006-26 (sections 2.1 to 2.4, 3.1, 3.2, 5.2),
  027-02 (sections 2 and 4), `TraceExport`'s tree and change code, and
  `TopDs`.
- Built: `java/build.sh`; `lake build` in `lean/contract/`. Traces were
  written with `TraceExport` directly (without `treecheck`) and checked
  with `contractcheck`; the hand-made faults of findings 1 and 2 were
  made from `mixed-1` of the small set (a trace without its TX 17, a
  non-empty one, fails, as it should).


# Log

2026-11-17, 14:48 to 15:40. The review, by a review agent of coord-1117
on the branch `030-06-review`, from `main` 2590ce30. Created the subitem.
