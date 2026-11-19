# 030-27. Java's reclaim steps checked on the traces

Created 2026-11-19 by Frans Lundberg. Status: done.

030-25 proved reclaim's `IterationOK` from a model of the iteration's
steps (`StepsOK`) and left as tested that Java's steps are the model's
steps; the traces checked that only through RC2 at each cut, which an
independent review of 030-24 classed as "checked in a weaker form" (the
trace did not mark an iteration's first step, so c ≤ s and the steps
themselves were not checked). This item builds the check that 030-25,
section 5, designs: a STEP line a step from the exporter, and its check
in `tracecheck`. Done by an agent, on the branch `030-27-step-check`.


# Result

- **The STEP line** (027-02, section 4): with the exporter's `steps=1`
  (and reclaim and `tree=1`), each step of reclaim has a line
  `STEP t0 c L L' eod` from its iteration's row in Java's memory: t0, the
  record of tStart; c, the first record at or after pCut (as on a CUT
  line); L and L', lastKey before and after the step (keys as format 3
  writes them, `-` for none); eod, whether the step's scan passed the end
  (the row done with the step's time as tEnd).
- **C-STEP** in `tracecheck` checks every STEP line at its step's state,
  on the tree model's reads (section 2), and every CUT line against its
  iteration's last step.
- **On the traces:** level 3's reclaim set (35 traces, 7 configurations,
  5 seeds): 1,014 STEP lines in 907 iterations (906 ended by a step with
  eod, one still going at a trace's end; so about a hundred iterations of
  more than one step), 11,943 old KVs met and checked put again, 775 CUT
  lines each at its iteration's last step; 0 failures. The fault test's
  10 faults each fail by their check's name.
- **What stays tested** after it (section 4): that the STEP line is the
  row in memory (the exporter, read in section 1), that Java's E is the
  model's only where it matters (C-STEP computes E itself), RC1 and RC4 at
  each cut (Java's arithmetic), and, as for every theorem of the
  contract, that Java's writer is PE and its records are the model's.
- **No finding about Java:** every step of every trace meets the model.


# 1. The exporter

java/stress/TraceExport.java, about 40 lines (`stepBegun`, `stepEnded`):

- At a step's record (the test hook `transExecuted`, inside
  `Reclaim.step`'s commit), the iteration in progress
  (`Reclaim.currentIteration()`, the row in memory) gives t0
  (`timeIndex(it.tStart)`), c (`idxByTpos.get(it.pCut)`) and L
  (`it.lastKey`): the step updates the row only after its commit
  (`it.set(next)`).
- At the next record, or at the end of the call (`afterCall`), the same
  row object gives L' (`it.lastKey`) and eod (`it.done` with
  `it.tEnd` the step's time: `step` sets both before the table store
  that ends the iteration, the next record). The line is added to the
  step's record, after FA and CUT, before PHYSCUT.
- Only with `steps=1`: the contract's checkers refuse a line of a kind
  not in their grammar (`Contract.lineKinds`, pinned in lean/contract),
  and they read treeconf.sh's traces, which have no STEP line.
  `conformance.sh reclaim` exports with `tree=1 steps=1` since this item
  and fails a reclaim trace without a STEP line. With and without
  `steps=1` the traces differ only by the STEP lines (compared on r-del,
  seed 1, but for the PHYSCUT lines, whose place depends on timing in
  both).


# 2. The check

lean/Check/Steps.lean (`reclaimStepFailures`, `stepCheck`; about 190
lines with four `#guard` tests), lean/Check/Tree.lean (the STEP line's
parser, `TStep`), lean/Check/Trace.lean (reads it over and counts it),
lean/TraceCheck.lean (C-STEP's report and verdict). The reads are the
tree model's (SIS/Tree/Read.lean) on P after the step's record, at the
times asked: the live keys after T(j) with their value nodes are the
model's scan of every key with `valueNodeFrom` (the model's `getFrom`
with the node's id in place of its value; 030-24's `idContents`); a
value node is old if the record that made it (its NEW line) is before c.

Per STEP line in TX i, at the step's state (after T(i - 1)):

- **STEP-chain**: L is the L' of the iteration's step before (none for
  its first step), with the same c; a new iteration comes after a step
  with eod and has a later t0.
- **STEP-c**: c ≤ t0 + 1, and t0 < i (the first step after T(t0)).
- **STEP-range**: E is the greatest key live after T(t0); the range is
  the live keys after L up to E; L' is L (no KV met) or a key of the
  range, and with eod the range's last key (the scan met all of it).
- **STEP-puts**: the step puts again (an `OP P` line) every KV of the
  range up to L' whose value node is old.
- **STEP-ops**: its operations have distinct keys and a put (the row).
- **STEP-line**: a STEP line in every record with a TOUCH line (a step)
  and in no other, one a record; **STEP-form**: the TREE line and the
  tree lines of every transaction, and every STEP line parses.

Per CUT line `CUT c f`: **CUT-steps**, the STEP line at R(f) has that c
and eod, and its iteration has no later step: the iteration of the cut
has its last step, with eod, at the cut's first available time (Java's
fa := tEnd).

The stop rule needs no check: the KVs met are the range up to L'. The
check runs only on a trace with STEP lines; a format 2 trace has none.
The report line:

    C-STEP reclaim's steps (bergdb 030-27): 0 of N transactions fail; S STEP
    lines, I iterations (E ended by a step with eod), K old KVs met and
    checked put again, C CUT lines with their iteration's last step

`conformance.sh` sums it over the reclaim set, and level 3 prints the sum.
C-STEP adds about nothing to `tracecheck`'s time (r-big, seed 1: 56 s
with and without the STEP lines).


# 3. The fault test and the runs

lean/test-traces/step-faults.sh, a step of level 3 (step 8, before
`conformance.sh reclaim`), exports a good trace (seed 1, 300
transactions, node size 14, retain 2; 14 STEP lines in 11 iterations,
three of two steps) and changes it by hand; each fault must fail by the
name of its check, and the good trace must pass with an iteration of more
than one step. It takes about a minute. Its output in level 3
(java/build/level3/step-faults.txt), each fault with the first failure
reported, cut at 100 characters:

    good: passes: 14 STEP lines, 11 iterations (11 ended by a step with eod), 297 old KVs met and checke
    noputs: fails, STEP-puts: T(45) 6 of 6 old KVs met not put again: [[20647455252896184, 0] (node 418)
    nextkey: fails, STEP-chain: T(219) lastKey before [25684930075820072], the step before left -
    eod: fails, STEP-range: T(209) eod, but lastKey after [25684930075820072] is not the range's last ke
    first: fails, STEP-chain: T(45) the iteration's first step with lastKey [25684930092597288]
    cut: fails, STEP-c: T(45) c 8 after t0 + 1 = 7
    outside: fails, STEP-range: T(45) lastKey after [8]: not L, nor a key of the range after - up to E =
    noeod: fails, CUT-steps: T(130) a new iteration (t0 104) before a step with eod in the one of t0 76
    nostep: fails, STEP-line: T(45) a step (a TOUCH line) without a STEP line
    extra: fails, STEP-line: T(3) a STEP line in a transaction without a TOUCH line
    badline: fails, STEP-form: T(0) 363 transactions, 363 with tree lines; bad lines: [line 4343: bad ST
    STEP FAULTS OK

The four `#guard` tests in Steps.lean check `reclaimStepFailures` on a
hand-made range at every `lake build`.

The runs at 2c16bbb9:

- `sh java/before-commit.sh`: BEFORE COMMIT OK (70 s).
- `sh java/stress/level2.sh`: LEVEL 2 OK (15 minutes).
- `sh java/stress/level3.sh`: LEVEL 3 OK (8 minutes); its step 8:

      C-STEP's fault test: 10 faults found, STEP FAULTS OK
      conformance: traces: 35, TRACECHECK OK: 35; C-CUT 0 of 775 CUT lines
        fail; traces without a cut: 0
      C-STEP: 0 of 21483 transactions fail; 1014 STEP lines, 907 iterations
        (906 ended by a step with eod), 11943 old KVs met and checked put
        again, 775 CUT lines with their iteration's last step; traces
        without a STEP line: 0


# 4. What stays tested

For `PE.pe_reclaim_reads_steps` (030-25), whose premise is that Java's
iterations follow `StepsOK`:

- **Checked on every step of the reclaim traces** since this item: the
  chain of lastKey within an iteration, c ≤ t0 + 1, the range against E
  computed from the trace, the rewrites of the old KVs met, distinct keys
  and a put, eod only when the range is met whole, and the cut at the
  iteration's last step with eod. So the review's "checked in a weaker
  form" is now checked step by step; c ≤ s follows from c ≤ t0 + 1 and
  t0 < s, both checked.
- **Still tested, not checked:** that the STEP line is Java's row (the
  exporter reads the row in memory; a wrong line would most likely fail
  the check, not pass it); Java's E itself (the check uses the E of the
  trace's tree at t0, so a Java E that differs where a key lies between
  the two would fail STEP-range or STEP-puts); the steps of runs with
  restarts and crashes (run A has none; 030-25, section 2, argues them;
  the reclaim tests gate them); and the configurations the traces do not
  reach (the reclaim set is small: 30 to 200 keys, node sizes 8 and 14).
- **Unchanged:** RC1 and RC4 at each cut (Java's arithmetic, C-CUT), and,
  as for every theorem of the contract, that Java's writer is PE and its
  records are the model's.


# Files

- java/stress/TraceExport.java (`steps=1`), java/stress/conformance.sh
  (the reclaim set with STEP lines, C-STEP's sum), java/stress/level3.sh
  (step 8: the fault test, the C-STEP line).
- lean/Check/Steps.lean, lean/Check/Tree.lean, lean/Check/Trace.lean,
  lean/TraceCheck.lean, lean/test-traces/step-faults.sh, lean/README.md.
  Nothing under lean/contract.
- 027-02 (the STEP line, section 4), 027-13 (REWRITES, the conformance
  checks, section 9), 030-25 (a note in section 5), 030's readme.


# Log

2026-11-19, 16:10. Started, on the branch `030-27-step-check` from
d7933bf0.

2026-11-19, 16:28. The exporter, C-STEP and its fault test (2c16bbb9).

2026-11-19, 16:54. Gated at 2c16bbb9: BEFORE COMMIT OK, LEVEL 2 OK,
LEVEL 3 OK (C-STEP 0 failures on 1,014 STEP lines). This item, 030's
readme and 030-25's note. Done.
