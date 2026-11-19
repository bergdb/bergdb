# 030-25. Reclaim's iteration proved

Created 2026-11-19 by Frans Lundberg. Status: done.

`IterationOK` (030-24) was the one premise of reclaim's top theorem
`PE.pe_reclaim_reads` about Java's iteration, argued (027-13, section 3,
REWRITES) and checked only through its consequence RC2 at each cut. Frans
decided to prove it (2026-11-19): a Lean model of the iteration's steps on
the contract's histories, as close to 027-13, section 1.4 as the proof
allows, and a proof that a history whose steps follow the model meets
`IterationOK`, so that what stays tested is that Java's steps are the
model's steps. Done by an agent of coord-1118, on the branch
`030-25-iteration-ok`.


# Result

For Frans, in plain words. Details in sections 1 to 6.

- **Reclaim's iteration is proved from its steps.** A history whose
  iteration's steps follow the model of 027-13, section 1.4 meets
  `IterationOK`: every key live before the iteration's first step whose
  value node was made before the cut is written again before its last step
  (`iterationOK_of_stepsOK`, given VAL-NEW, which PE meets). So the
  argument of REWRITES is now a theorem.
- **The model of a step** (`StepsOK`, section 1): each step is one
  transaction; its scan reads the latest state, from the key after lastKey
  up to E, the greatest key live at tStart; it may stop before a KV (the
  value limit) or after one (the split, the size) by any rule; it puts
  again every KV met whose value node was made before the cut, and puts its
  row, one operation a key; lastKey becomes the last key met; the last step's
  scan passed E or the last key. Between steps, any transactions.
- **The edge cases** all fall out of one argument (section 3): a key with
  an old value node was live, with that node, from tStart on (a later put
  makes a new node, and a node is made once), so it is at most E and every
  step's scan meets it until it is written: the value-limit stop leaves
  lastKey below it, the split and size stops leave it at or after it, a key
  deleted or put again is written, a key put behind the cursor is not old,
  an empty scan (no key at tStart, or lastKey at E) is the last step, and a
  last step whose end a crash lost is an ordinary step.
- **The top theorem with the steps** (`PE.pe_reclaim_reads_steps`): for
  every history PE writes, with cuts whose iterations' steps follow the
  model, Java's get and scan after the run with handles, evictions and
  restarts from the cut streams are right at every time from the first
  available time on. It no longer needs `IterationOK`, nor a key live at
  the iteration's end: the last step puts its row.
- **Not vacuous:** a history PE writes, of five transactions, with an
  iteration of two steps that follow the model, in which all four keys
  with old values are written during the iteration: three by the steps'
  rewrites, one by a user transaction between them (`StepsExample`).
- **What stays tested:** that Java's steps are the model's steps (section
  4; not checked on the traces today, a check is proposed in section 5),
  RC1 and RC4 at each cut (Java's arithmetic, as before), and, as for every
  theorem of the contract, that Java's writer is PE and its records are the
  model's.
- **Found:** Java's steps agree with 027-13, section 1.4, in everything the
  model needs; one stale parenthesis in 027-13 and in `Reclaim.step`'s
  comment about rows without E (section 6).


# 1. The model of the steps

In Contract/ReclaimSteps.lean, on the contract's histories (`BHist`):

- **An iteration** (`Iteration`): its cut c, its start t0 and its steps. A
  value node made by a transaction before c is "old" (`oldNode`; Java: its
  position is before pCut, since a value node is stored in the record of the
  transaction that made it, 030-22, section 2.1, and c is the first record
  at or after pCut). E is the greatest key live after transaction t0
  (`endKey`; Java's `lastKeyAt` at tStart), none if no key is.
- **A step** (`IterStep`): its transaction, the history's (j + 1)-th, and the
  stop rule its scan followed. It holds the write lock, so its scan reads the
  tree after transaction j, at time j: the latest state (Java's lookup time
  `Long.MAX_VALUE`).
- **The scan** (`stepScan`, `scanRange`, `scanWalk`): the live keys with the
  ids of their value nodes (`idContents`, 030-24), after lastKey (every key
  for the first step) and up to E inclusive, in key order. At each KV the
  rule says stop before it (Java: the value limit, the KV is the next step's
  first), stop after it (Java: the split, the size) or go on. The scan's
  result: the KVs met and `eod`, whether it passed E or the last key without
  a stop (Java's `StopCondition.eod`, which `Dag.getMany` calls only when the
  walk runs out, never after a STOP).
- **lastKey** (`nextKey`): the last key met; unchanged if none.
- **The step's transaction** (`StepTx`): it puts every KV met whose value
  node is old (the rewrites), it puts a key (the row), and its operations
  have distinct keys (one KV a key; the row replaces a rewrite of its key).
- **The steps** (`StepsFrom`, `StepsOK`): there is at least one; c ≤ t0 + 1
  (pCut is the previous iteration's pStart, or pStart for the first, so at
  most pStart, the stream's length after transaction t0); the first step
  comes after transaction t0, each next one after the one before; each scans
  from the lastKey that the one before left (none for the first); the last
  one's scan has `eod`.
- **Between the steps**, any transactions of the history: the user's,
  reclaim's begin and table stores, the row stored again (027-13, 1.4, 4b),
  `maintain()`'s fillers. A step's own scan and commit are one transaction.

What the model leaves out, and why it does not matter for `IterationOK`:

- **The stop rules' arithmetic** (MIN_STEP, MAX_STEP, W, the counted
  bytes, the value limit, the reserve in index nodes): the model quantifies
  over every rule; any rule that stops before or after a KV gives a prefix of
  the scan's range, and the proof uses only that.
- **When a step runs** (the allowance, `maintain()`'s M2) and **when an
  iteration begins** (R div 4, 2 sd, M1): only that the first step is after
  t0 and the steps are in order.
- **A non-last step with `eod`**: allowed, since a crash can lose the end's
  table store after a last step (`testCrashBeforeIterationEnd`); the next
  step then ends the iteration.
- **A step that meets no KV**: allowed (Java's first KV is always met; a
  stop before needs a KV kept already).
- **Exactly which operations a step has**: the model asks for the rewrites,
  a put (the row) and distinct keys; Java's step has exactly the rewrites and
  the row, which meets it. The rewrites' values (the same value) do not
  matter.
- **Puts of KVs met whose value node is not old**: allowed (Java's step does
  not make them; `IterationOK` does not care).


# 2. Restarts

The model's history is the history of the commits; a restart adds no
transaction. The steps of a run with restarts are steps of the model:

- A step's row, with lastKey, E, pCut and tStart, is a KV of the step's own
  transaction (`Reclaim.step`, `b.putCore(currentKey, ...)`), so it is
  committed with the step's rewrites or not at all; a step whose commit fails
  (a crash, a `RerunException`) leaves lastKey as it was (`it.set(next)`
  comes after `db.execute`).
- A start reads the row (`initFromDb`, 027-13, section 1.9): the current row
  replaces the table's row with the same pStart if neither is done. Every
  store of either holds the row in memory, and the last store of the current
  row is by the last step (or by 4b's row stored again, which keeps lastKey),
  so the next step after a start scans from the lastKey of the last committed
  step, with the iteration's E and pCut: the chain of `StepsFrom`.
- A crash between the last step and the table store that marks the
  iteration done leaves that step an ordinary step of the model: the next
  step, after the start, scans from its lastKey and is the last.
- An older iteration's current row (its last step stores it with done
  false) does not replace the table's row of that iteration, which is done.


# 3. The proof

In Contract/ReclaimSteps.lean, section 2; about 400 lines.

- **The invariant** (`step_covers`, `stepsFrom_covers`): fix a key k that
  names an old value node y after transaction s - 1. After each step, if k is
  at or before the step's lastKey, k has been written by a transaction from s
  on. A step keeps it: if k was written before the step, so it stays; if
  not, k still names y at the step's state (VAL-NEW, `ValNew.keep`), so it is
  live there; if it is at or before the old lastKey, the steps before wrote
  it; otherwise it is in the step's range, and if it is at or before the new
  lastKey it is in the prefix the scan met (the range is in key order,
  `scanRange_sorted`, `mem_of_prefix_le`), so the step puts it.
- **The last step** met its whole range (`scanWalk_eod`), so it puts k if no
  step before covered it, provided k is at most E.
- **E's bound** (`old_live_before`, `upTo_endKey`): k named y at t0. A write
  of k after t0 and before s would be a put, whose new node k names
  afterwards (VAL-NEW), or a delete, after which k is not live; the last such
  write decides, and a put would have made y after t0, but y was made before
  c ≤ t0 + 1. A node is made once (`MeetsFull.made_once`): a node a
  transaction makes is no node of the tree before it, so none of the model's
  structure before it (the bridge's `fresh`), which holds every node made
  earlier (`BHist.P_isData`). So k was live at t0 and is at most E.
- **The edge cases**: the value-limit stop (stop before: the KV is not met,
  lastKey stays below it, the next step's scan begins below it); the split
  and size stops (stop after: the prefix ends at the KV); keys deleted or
  put again during the iteration (written, so covered); keys put behind the
  cursor (their value nodes are new, so not old; a key with an old node was
  live from t0 on, so a step met it); an empty scan (the range is empty when
  E is none or lastKey is at E, so `eod` holds); E's bound above; the begin's
  table store and other transactions between steps (any transactions).
- **The theorem** (`iterationOK_of_stepsOK`): `IterationOK h c s e` for every
  s from t0 + 1 (030-22's s, the record at pStart) to the first step (030-24's
  s), with e the last step; `iterationOK_steps` takes s the first step.
- **A key live at the end** (`stepsOK_live`): the last step puts its row, one
  operation a key, so its key is live after it (the writer's contract).


# 4. The top theorems, and what stays tested

- `CutsMeetSteps`: as `CutsMeetIter` (030-24), with an iteration whose steps
  follow the model in place of `IterationOK` and of a key live at its end:
  at each cut mark, the cut is at or after the earlier ones, and some
  iteration with that cut has `StepsOK`, its last step at most the first
  available time, and RC4. `cutsMeetIter_of_steps` gives `CutsMeetIter`
  from it with VAL-NEW.
- `reclaim_java_reads_steps` (any history with `MeetsFull`, K-LEVEL and
  VAL-NEW) and `PE.pe_reclaim_reads_steps` (every history PE writes; VAL-NEW
  by `PE.pe_valNew`): Java's reads after the run with handles, evictions and
  restarts from the cut streams are right from the first available time on.
  The statements of 030-24 are unchanged; these are added beside them.
- **What stays tested** for reclaim's part of the aim:
  - that Java's iterations are the model's: c ≤ t0 + 1 (pCut at most
    pStart), E the greatest key live at tStart, and each step as section 1
    says. Not checked on the traces today: the trace marks a step's record
    (`kind=step`) and has its operations, but not its iteration, tStart, E,
    lastKey or `eod` (section 5). Its consequence RC2 is checked at every cut
    (C-CUT; 030-23), and the reclaim tests gate it (027-13, section 3,
    REWRITES). An independent review of 030-24 (2026-11-19) classed the
    check of `IterationOK` as "checked in a weaker form" for the same reason:
    the trace does not name the iteration's first step;
  - RC1 and RC4 at each cut (Java's arithmetic; `tracecheck` since 030-23).
    The same review noted that c ≤ s is not checked, as s is not in the
    trace; in the model, c ≤ s follows from c ≤ t0 + 1, part of `StepsOK`;
  - as for every theorem of the contract, that Java's writer is PE (026-25)
    and Java's records are the model's (the trace checkers).


# 5. Checking Java's steps on the traces

Not built (more than a few lines). What a check would need:

- **The trace has:** each record's kind (`kind=step` in the TX comment), the
  step's operations (OP lines), the nodes made (NEW lines, so `madeAt` and
  `oldNode`), the tree at each time (so `idContents` by id), and each cut c
  with its first available time (CUT lines).
- **It lacks:** which iteration a step belongs to, t0 (or E), and for each
  step lastKey before and after and `eod`. The row's text holds lastKey, E,
  pCut and tStart, but the trace has only its value's hash.
- **The check:** one line a step from the exporter, from the row in memory
  (`STEP t0 c L L' eod`, keys as in format 3), about ten lines in
  `TraceExport`; and in `tracecheck`, per step at its state: L is the
  previous step's L' within the iteration (none for its first), E is the
  greatest key live at t0, c ≤ t0 + 1, L' is a key of the range (or L), the
  step puts every key of the range up to L' whose value node is old (all of
  the range if `eod`), its operations have distinct keys and a put; and per
  CUT, the iteration with that c has its last step, with `eod`, at the CUT's
  first available time. The stop rule needs no check: the KVs met are the
  range up to L'. About 100 to 150 lines of Lean with its fault tests.
- **A cheaper check**, which the review proposed: one number per iteration,
  its first step s (or t0), and `IterationOK` itself at each cut: every key
  live before s whose value node is before c is written from s to e. It
  checks the premise 030-24 uses, not the steps.


# 6. Java against 027-13, section 1.4

Read for the model at `c0e2afaf` (`Reclaim.step`, `transactionCompleted`,
`maintain`, `lastKeyAt`, `IterationInfo`; `Dag.getMany`): the scan, its
range, the three stops, lastKey, the rewrite rule, the row in the step's
transaction and the end are as 027-13 says. One stale text, no bug:

- 027-13, section 1.4, step 1, "(to the last key for a row stored without E,
  before 026-05)", and `Reclaim.step`'s comment ("A row stored before 026-05
  has none (null): its scan is not bounded so"): since 028-15 no such row is
  read. `IterationInfo.deserialize` refuses a row without `endKey`, and
  `IterationInfo.endKey`'s comment says so; a step with a null `endKey`
  would throw at `it.endKey.length`. A todo for 028, not changed here.


# 7. Files and gates

- **The branch** `030-25-iteration-ok`, from `main` c0e2afaf, in
  lean/contract only but for this item, 030's readme and 027-13:
  - 2d2e3021: Contract/ReclaimSteps.lean (the model, the proof, the top
    theorems; 647 lines) and Contract/ReclaimStepsExample.lean (the example;
    83 lines); Axioms.lean lists 191 theorems (182 before); statements.pin
    with the new file and Axioms.lean's new hash.
- **Gate:** `lean/contract/gate.sh c0e2afaf` at 2d2e3021: GATE OK (191
  theorems, the standard axioms only; 85 files of the closure, 99 pinned;
  pinned files changed since c0e2afaf: Axioms.lean, by added lines, and
  ReclaimSteps.lean, new). At the head (6a409cf2, this item, 030's readme
  and 027-13): `gate.sh c0e2afaf` passes steps 1 to 3 and 5, and step 4
  lists only items/027-algorithms/13-reclaim.md, which the gate does not
  allow by design; `gate.sh` without a base: GATE OK. No pinned statement
  of 030-24 or before changed. Java and lean/
  outside lean/contract did not change; the checkers' package
  (lean/contractcheck) imports neither new file.


# State

2026-11-19, 16:00. **Done.** `IterationOK` is proved from a model of the
iteration's steps (`iterationOK_of_stepsOK`), and the top theorem for PE
takes the steps in its place (`PE.pe_reclaim_reads_steps`); gated (section
7). 027-13 and 030's readme updated. Possible next steps: the trace check
of section 5 (a STEP line and its check in `tracecheck`, or the cheaper
check of `IterationOK` with the iteration's first step); the stale text of
section 6, a todo for 028.


# Log

2026-11-19, 15:29. Started, on the branch `030-25-iteration-ok` from
c0e2afaf.

2026-11-19, 15:47. The model and the proof built: `iterationOK_of_stepsOK`,
`PE.pe_reclaim_reads_steps`, the example; GATE OK against c0e2afaf at
2d2e3021.

2026-11-19, 16:00. This item, 030's Files list and 027-13 (REWRITES,
T-SCHEME, sections 5 and 9). Done.
