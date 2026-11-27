# 031-06. Landing notes: steps 0 and 1

2026-11-27, on the branch `031-06-landing` of a clone of `main` (outside the
repository), from `05c002ad`. Notes of the landing's work for the lead, who
lands the item's text; this file does not replace the item's `readme.md`.

## Step 0: the port

* **What came:** the prototype's `java/` as one change: the diff from the
  merge base of `031-06` and `main`, `9e72d0d5` (main of 2026-11-26), to
  `fa11d15f`, which carries 031-04's `maintain(int budget)` and the witness
  a, 031-05's maintenance decided from the stream, and 031-06's one record
  an action with the copy mark. The prototype changed nothing in `lean/` or
  the scripts. Applied with a three-way merge on `main` at `05c002ad`.
* **Conflicts with today's `main`:** one, the Javadoc of
  `Database.maintain(int)`, where 028-62 had corrected `maintain()`'s
  400 kB to the stream's; the prototype's text is taken, which describes
  the pass by parts. 028-69 (the crypto code removed) and 028-60's part 2
  (the tail of zeros) touched none of the prototype's lines; the build and
  the tests found no other conflict.
* **Prototype-only code removed:**
  * `Db.maintain(int budget, int maxParts)`, which the probes called by
    reflection: now the test hook `Db.TestHooks.maintainMaxParts()`, read
    once at a call's start (default: no limit). The probes `P2CrashProbe`,
    `FaultProbe` and `ConcProbe` need a small change for it (a field
    `maxParts` and the hook in place of the reflective call). The item's
    `probes/` land with the item, not in this branch; the change that the
    gate below ran is the appendix's diff.
  * `DbBuilder.maintenanceNone()` is package-private: for the Core's tests
    and probes, not in the API.
  * Two comments that named "031-05's prototype" name 031-05 and 031-06.
  * No system property of the prototype was left in `java/src`
    (`proto315.*` went with 031-05's D1/D2 switch in 031-06's prototype).
  * Kept: the hooks `TestHooks.beforePlan` and `beforeApply` (the probes use
    them; `TraceExport` uses `beforeApply` since step 1), and
    `Reclaim.rowsForProbe()` (the unit tests use it).
* **Gates:** `BEFORE COMMIT OK (63 s)`. `P2CrashProbe` with the item's
  `sweep.sh` (its 23 configurations) on the ported jar: 27,720
  interruptions, 27,720 the same, 0 different, the start's memory the
  running database's at every one; 567 torn records continued the same; the
  23 reference streams have the digests of the item's `runs/sweep.txt`, one
  for one. With the same adapted probes on the jar of step 1: `faults.sh`
  (`FaultProbe`, six seeds, faults at four points), the item's
  `runs/faults.txt` line for line, its six reference digests the same, bad
  0; `conc.sh` (`ConcProbe`, threads, then a one-thread replay whose parts
  are `maintain(B)` calls with `maintainMaxParts()` 1): ten runs, the replay
  gave the same stream in all ten.

## Step 1: the conformance (review, F1)

The checks of a record that carries a step, as they are now. A mixed record:
a commit's record (or a part's) that holds its action's operations, a step's
copies, reclaim's row and maybe its table, one operation a key.

* **The trace format** (027-02, updated with the code): a copy is an `OP C
  key v` line, a put whose value node has the copy mark; the exporter reads
  the mark from the record's bytes (`StoredValueNode.isCopy`) and fails the
  trace (an `ERROR` line) unless the marked keys are the plan's copies
  (`Maintenance.Plan.copyKeys`). With `steps=1` every record has its action
  as submitted, `ACT P key v` and `ACT D key` lines, after its OP lines: a
  user transaction's as the exporter's workload built it, before Db sees it;
  BergDB's own actions (a setter's, the creating start's) from the Trans that
  Db executed; none for a part. `OP C` is in the grammar of the contract's
  checkers; `ACT` is not (as `STEP`, only in `steps=1` traces, which those
  checkers do not read). The comment line of a TX gives `kind=step|user|part|
  table` and `copies=N`. The trace's version stays 3.
* **TraceExport:** the OP C and ACT lines; the STEP line made in the step's
  own record, with lastKey before the step from the row before the record
  (`Db.TestHooks.beforeApply`, the hook kept from the prototype) and L' and
  eod from the plan's row (`Reclaim.RecordPlan.next`, `eod`), checked
  against the row after the record; `crash=K` after the K-th step's record
  of any kind (commit or part), and no deferred STEP line after a crash.
  `tracecheck` filters the ACT lines before its pinned parser
  (lean/Check/Trace.lean), as it does RESTART and RESUME.
* **C-STEP** (lean/Check/Steps.lean, `reclaimStepFailures`), per STEP line,
  at the state before the record (after T(i - 1), which the scan reads):
  STEP-chain, STEP-c and STEP-range as before; STEP-puts: every old KV of
  the range up to L' is written by the record, by a copy, or by an operation
  of the action at its key (a put or a delete), or by reclaim's row or table
  there; STEP-values: every copy writes the value the scan read; STEP-ops:
  one operation a key, the row put (not as a copy), every copy of an old KV
  met. **STEP-action** (new, `actionFailures`), for every record of the
  trace, against its ACT lines: the operations that are not copies are the
  action's, each operation of the action among them as submitted (a put with
  its value, a delete as `OP D` or `OP N`), and every other one is a put at
  a key of reclaim's reserved prefix `/#i/dreclaim/` (`reclaimReserved`, the
  contract's `reclaimKey`); no copy at a key the action writes; copies only
  in a record with a TOUCH line. So on a mixed record C-STEP verifies that
  the record's effect outside reclaim's keys is its action's, as submitted,
  plus copies that put back the values the scan read, and that every old KV
  met is written.
* **C-STEP's fault test** (lean/test-traces/step-faults.sh): the 18 faults
  of before, adapted (the copies are OP C lines; `del` and `put` now fail by
  STEP-action, not STEP-ops), and 5 new ones: `unmark` (a copy without the
  mark), `mark` (an action's put marked as a copy), `actval` (an action's
  put with another value), `actdrop` (an action's put left out), `copyuser`
  (a copy in a record without a step); the good trace must have a step in a
  commit's record with an action. The second good trace (restarts and
  crashes) is now conformance.sh crash's c-vals: with one record an action,
  the old small configuration ends every iteration in one step, so no
  iteration spanned a restart. `STEP FAULTS OK`: the good trace has 16 STEP
  lines in 11 iterations, 310 old KVs met, 301 copies, 303 records checked
  against their actions (1,300 operations); the second, 31 STEP lines, 88
  restarts (10 crashes), 14 iterations with a step before a restart and the
  next after it.
* **The tree model** (lean/Check/Tree.lean, TreeRun.lean): `OP C` is a put,
  and its key is a copy (`TTx.copies`); a step's touch keys are its copies'
  and reclaim's row (`stepTouchKeys`, Java's `Plan.touchKeys`): C-T5 compares
  `touchOf` of those with the TOUCH line, C-T9 runs the model with them. The
  other checks take the copies as puts, as the writer does. `treeconf.sh
  reclaim 1`: TREECONF OK, 105 touches, C-T5 and C-T9 0 failures.
* **The contract checkers** (`contractcheck`, `bridgecheck`; Contract/Trace.lean
  and Contract/Complete.lean): `OP C` read as a put, in the grammar.

* **The contract** (lean/contract, with Mathlib), proved, no `sorry`:
  * `StepTx` (Contract/ReclaimSteps.lean): every old KV the step's scan met
    is written by the record, `kv.1 ∈ ops.map Op.key` (a copy, or the
    action's put or delete; it was `∈ putKeys ops`); the row put; one
    operation a key. Its fourth conjunct, `StepOpOK` of every operation (a
    put of an old KV met with its value before, or the row; no delete), is
    gone from it, and with it StepTx's index j, which only that conjunct used.
    `step_covers` takes the key as written from the first conjunct directly.
    `iterationOK_of_stepsOK`, `reclaim_java_reads_steps`,
    `pe_reclaim_reads_steps`: proofs unchanged; their statements change
    only through `StepTx`.
  * Contract/ReclaimValues.lean: maintenance is marked per operation,
    `maintenance : Nat → Op → Bool` (the copy mark; until now per
    transaction). `StepOpOK` (moved here) is a copy: a put of an old KV met
    with the value the key had before the record; never a delete.
    `MaintenanceOK`: every record has one operation a key, and every marked
    operation is a copy of some step's scan at that record. The reference
    `userTransactions` keeps, of each record, the operations outside
    reclaim's prefix that are not copies: the action's. New:
    `applyOps_drop_copies` (on a map in key order, with one operation a key,
    marked puts of pairs the map holds change nothing) and
    `record_preserves_users` (a record's effect on the user keys is that of
    its operations without the copies). `user_contents_at`, `user_refMap`,
    `reclaim_user_reads_steps` and `pe_reclaim_user_reads_steps` are proved
    with the per-operation marks; the last two take `CutsMeetSteps`, as
    `CutsMeetMaintenanceSteps` (steps marked as maintenance transactions)
    has no meaning with marks per operation and is gone. Gone:
    `StepTx.put_value`, `StepTx.no_delete`, `StepTx.preserves_users`,
    `reserved_preserves_users`, `applyOps_existing` (unused now).
  * What is proved and what is tested: proved, that removing the copies
    (marked operations that put back the values before the record, at keys of
    no other operation) leaves every user read as the reference of the
    unmarked operations; tested, not proved, that the unmarked operations of a
    record are its action as submitted (C-STEP's STEP-action on traces) and
    that Java's marks are the copies (the exporter's check against the plan,
    and STEP-values, STEP-ops).
  * Examples (Contract/ReclaimStepsExample.lean, ReclaimValuesExample.lean):
    the second step is a commit's record, whose action deletes an old KV the
    step meets (so no copy of it) and puts a key above E; the steps still
    follow the model and give `IterationOK`; the reference holds the action's
    delete and put. `wrong_value_rejected`, `unmet_copy_rejected`,
    `delete_copy_rejected` (on `StepOpOK`), `missing_row_rejected`,
    `unwritten_rejected` (on `StepTx`), `mixed_step` (the commit's record
    meets `StepTx`).
  * The parsers: `OP C` in Contract/Trace.lean (a put) and
    Contract/Complete.lean (the grammar).
  * `gate.sh`: GATE OK; 254 theorems, as before, on the standard axioms only
    (`propext`, `Classical.choice`, `Quot.sound`: the gate's list is
    unchanged). Axioms.lean's list of theorems: removed `StepTx.put_value`,
    `StepTx.no_delete`, `StepTx.preserves_users`,
    `CutsMeetMaintenanceSteps.cutsMeetSteps`,
    `ValuesExample.extra_put_rejected`, `ValuesExample.extra_delete_rejected`;
    added `applyOps_drop_copies`, `record_preserves_users`,
    `ValuesExample.unmet_copy_rejected`, `delete_copy_rejected`,
    `unwritten_rejected`, `mixed_step`. `statements.pin` (pin.sh): five
    pinned files changed (Axioms.lean, Contract/Complete.lean,
    ReclaimSteps.lean, ReclaimValues.lean, Trace.lean); 123 files of the main
    theorems' closure, 144 pinned, as before.
* **Lines changed** (added, removed), from the port's commit: lean/Check/Steps.lean
  130, 65; lean/Check/Tree.lean 56, 4; lean/Check/TreeRun.lean 4, 2;
  lean/TraceCheck.lean 18, 11; lean/TreeCheck.lean 3, 1;
  lean/test-traces/step-faults.sh 51, 23; lean/contract/Contract/ReclaimSteps.lean
  37, 40; ReclaimValues.lean 133, 118; ReclaimStepsExample.lean 11, 7;
  ReclaimValuesExample.lean 55, 34; Contract/Trace.lean 6, 0;
  Contract/Complete.lean 4, 0; Axioms.lean 6, 6; statements.pin 5, 5;
  java/stress/TraceExport.java 132, 73; java/stress/conformance.sh 5, 4;
  027-02 86, 28.

**Gates** (on F53, 2026-11-27, from 15:25; other sessions' work on the
machine; functional runs):

* `lean/test-traces/step-faults.sh`: `STEP FAULTS OK`, 23 faults found.
* `java/stress/treeconf.sh reclaim 1`: `TREECONF OK`; C-T5 and C-T9 0
  failures over 2,515 transactions with 105 touches.
* `java/stress/level3.sh` (full, 10:51 min): `LEVEL 3 OK`. Step 8:
  conformance reclaim, 40 traces, TRACECHECK OK 40, C-CUT 0 of 869 CUT lines
  fail; C-STEP 0 of 23,127 transactions fail, 1,370 STEP lines (557 of them
  in commits' records, the rest in parts' records of the `maint` sets), 1,042
  iterations, 14,954 old KVs met and written by their record, 14,679 copies
  with the value read, 23,087 records against their actions as submitted
  (55,718 operations); 30 of the 40 traces have a step in a commit's record
  with an action. Crash: 15 traces, TRACECHECK OK 15, C-STEP 0 of 5,593
  fail, 409 STEP lines (209 in commits' records), 8,785 copies, 5,578 records
  against their actions; STEP-resume 925 restarts (135 crashes), 68
  iterations with a step before a restart and the next after it. (The copy and
  action counts are from the run's check files, summed with the summary of
  `conformance.sh` as committed after the run; the run printed the old
  summary's words.)
* `lean/contract/gate.sh`: `GATE OK` (above).
* `java/stress/level2.sh` (full, 12:56 min): `LEVEL 2 OK`. Step 0, the pins:
  144 files with their pinned hashes. Step 8, treeconf: reclaim 7,545
  transactions with 310 touches, C-T5 and C-T9 0 failures (with small 7,240
  and drain 14,120 transactions). Step 8b, `check.sh small drain`: CONTRACT OK,
  with its fault tests, bridge-faults.sh among them on the reclaim trace
  `r-del-1` (193 `OP C` lines). Step 8c, pecmp: 0 differ in the small, drain
  and reclaim sets. A first run of level2 (15:44) failed at its unit tests, in
  `ReclaimMaintainTester.testCommitGoesBeforeTheNextPart` (031-04's test of the
  lock's handover: "the call gives way, expected TIMED_WAITING, got
  RUNNABLE"); the test passed alone six times, six runs at once, in both runs
  of before-commit.sh, in level3's unit tests and in the second level2 run.
  It decides by sampling a thread's state, which a loaded machine can keep
  RUNNABLE (a thread that waits for a core); it is the prototype's test, not
  changed here (later steps).
* `java/before-commit.sh` at the end: `BEFORE COMMIT OK (65 s)`.
* `java/stress/level4.sh quick` (not required; 1:54 min): `LEVEL 4 OK`, its
  conformance with eviction 18 traces, TRACECHECK OK 18.

## What depends on Frans's two answers

Frans decided at 14:36: `maintain(int budget)` replaces `maintain()` in the
Core and Pub API in 2026.7; 2026.7 does not open a 2026.6 database (a new
format version, refused with a clear message, no upgrade path).

* `maintain(int budget)` in place of `maintain()`: as the prototype has it.
  `Db.maintain(int)`, `Database.maintain(int)` and `DatabaseImp`, `Db`'s and
  `Database`'s `getStreamSize()`, the stress apps (`BackToEmpty`,
  `KillEmpty`, `SlowDrive`, `D2ScanHistory`, `D3ObjectIndex`), `AppRecord`,
  `CountGates`, `TraceExport` (`maintain(Reclaim.MAINTAIN_MIN_BUDGET)`).
  Nothing to change in the code; the Javadoc still says `maintain()` in a
  few places as the method's name (`Database`, lines 367, 553, 589). The
  documents (027, README, releases/next.md) are not part of this landing.
* 2026.7 refuses a 2026.6 database: not built. The prototype writes
  `StoredTrans.RECORD_FORMAT` 8, as 2026.6 does, and marks a copy in byte 6
  of a value node (`StoredValueNode`), which 2026.6 skips: today this code
  opens a 2026.6 stream, and 2026.6 opens one of this code and reads its
  copies as plain values (`transactionInfo()` differs). What the decision
  needs: `RECORD_FORMAT` 9 (`StoredTrans`, checked in `NodeStream` and the
  parser, written in the header), whose refusal message exists
  (`StoredTrans.formatRefused`: an older or a newer BergDB); 2026.6 reads
  format 8 only and so refuses format 9; the tests and `CorruptStreamTester`
  that build records of format 8 by hand; the item's question Q5 then has
  its answer (the record's format, not the value node's or the meta
  block's, unless Frans wants those too). Built in step 2 (below).

## For the later steps

What this work met that bears on the steps not taken here (F2 to F7, the
kept times, the documents):

* **The step's size (F3, F4).** With one record an action a step rides on a
  commit whenever the commit's allowance passes `MIN_STEP_SIZE`: in the
  small configurations every iteration now ends in one step. C-STEP's fault
  test's second trace (30 keys of 20 bytes, restarts every 10 actions) no
  longer had an iteration across a restart and now uses the crash set's
  c-vals; a change of the step's size or of its allowance should keep at least
  one configuration of each set with iterations of several steps (level 3
  prints the counts: 1,042 iterations for 1,370 STEP lines in the reclaim set).
  In the `maint` sets every step is a part's (0 in commits' records).
* **The admission and the record's room (F5, F6).** The contract's
  `MaintenanceOK` and C-STEP's STEP-ops require one operation a key in a
  record (`Db.merge`, which fails the database on a key in both): a change
  that admits or trims the step's KVs by the room must keep the merge's rule
  and the drop of a copy at a key the action writes.
* **What the trace reads of the prototype's code.** `TraceExport` takes
  lastKey before a step from `Db.TestHooks.beforeApply` and L' and eod from
  `Reclaim.RecordPlan.next` and `eod`, and the copy keys from
  `Maintenance.Plan.copyKeys` (checked against the copy marks of the record's
  bytes). A refactoring of the plan (F2's charge, F7's reserve as a constant,
  Q6's cheap first test) must keep these, or change the exporter with it.
* **The action as submitted.** STEP-action compares a record with the
  exporter's own copy of the workload's transaction, so a change in what Db
  writes for an action (a transformation, a merge) shows there; for BergDB's
  own actions (setters, the start's record) the exporter takes the Trans Db
  executed, which is weaker; a part's action is empty.
* **F9.** The copy mark is in the bytes, and the exporter reads it with
  `StoredValueNode.isCopy`; `Db.getTrans` and `transactionInfo` can tell a
  record's copies the same way.
* **The format (Frans, 14:36).** `RECORD_FORMAT` 9 is the change that
  refuses a 2026.6 database; the traces' format (`TRACE 3`) did not change, as
  `OP C` and `ACT` are new lines that the old checkers refuse or ignore
  (`tracecheck` filters ACT before its pinned parser).

## Step 2: the record's room by a check, the format, the reserve

2026-11-27, 16:05 to 17:10, on the same branch, rebased on `main` at
`a9d87266`. The review's F5, F6 and F7; the record format for Frans's
decision of 14:36; the lock-handover test.

### The record's room (F5)

The rule, as built:

* **What.** Every record's index nodes, those its action and its
  maintenance make dirty or create together, are within
  `StoredTrans.dirtyLimit()`, 15/16 of the record limit: the bound that
  005-31 kept for a transaction, now for the record, so that a later
  record takes them whole (`TransSeq.take` takes a record's set whole or
  not at all). An action alone is admitted within
  `StoredTrans.actionDirtyLimit()` = `dirtyLimit()` less
  `stepDirtyRoom()` (a sixteenth of the record limit): 7/8 of it, so a run
  of the largest actions leaves every step that room (Codex's E5).
* **When, by whom.** (1) The admission, `Db.checkDirtyNodes` and
  `checkDirtyNodesAfterKeyTransformations`, under the write lock before
  the go point: the action against `actionDirtyLimit()`, refused as
  before (`DbException`, 005-31). (2) The plan, `Reclaim.plan`, before the
  go point: `Db.recordDirtyFits(action, plan)` counts the record's KVs
  merged, as `countDirtyNodes` counts a transaction (the cheap test, a sum
  over the KVs; the walk of all the record's keys, `Dag.dirtyNodeBound`,
  if the cheap test is over). Over `dirtyLimit()`: the plan is made again
  with a step of its first KV to copy only (015-50's rule: the next old
  KV); still over, a commit's record carries no step (B, P and C as due),
  and a later record whose action leaves more room carries it; a part's
  step keeps its first KV, so that `maintain()` always moves the
  iteration. (3) The check, `Db.checkTakeable`, in `store()` after the take
  and the nodes it keeps dirty (`handleStillDirtyNodes`), before the
  append: the record's got-dirty set, each node counted at its largest
  with its entry, within `StoredTrans.takeRoom()` = the record limit less
  a record header and two top nodes, the room of a later record with no
  KVs (an empty commit, a part's take, M4). Over it: a `Bug`, which fails
  the database (P7) with nothing of the record written. That is where a
  set that no later take could take is detected; until now nothing
  failed and the startup pos stood before it for good.
* **Why this one.** The admission alone cannot count the step (it runs
  before the plan); a lowered internal limit for the transaction alone
  (Q3 (b)) leaves the step's own count unchecked, which F6's long key
  passes; sizing the step by arithmetic needs a bound on the keys it
  copies. Counting the record as one transaction reuses 005-31's count,
  is from the actual keys, costs a sum over the KVs when it fits, and
  keeps one rule for every record. The reserve of 1/16 is Q3 (b) for the
  index nodes only: the record cap and the value limits are as in step 0.
* **Checked.** `ReclaimRoomTester` (f-tests, about 3 s): two sustained
  runs at lowered limits (100 kB at node size 8, 200 kB at node size 30),
  with 3,000 cold keys, 20 cold keys of 60 segments under "/#" and a third
  of the actions near or over the action's limit: no failure, the
  startup pos moves in every window of 300 actions, 9 and 15 cuts, the
  stream kept in the last third at most 1.3 times the middle third's,
  the values the model's after a restart; the room made 238 and 122
  plans again with the step's first copy, and left 2 and 4 of those steps
  out of a commit's record; the
  largest set 366 nodes, 70,912 bytes at the largest sizes (dirtyLimit
  93,750) and 330 nodes, 179,808 bytes (187,500); no record's set over
  dirtyLimit. `testUntakeableRecordFails` (unit): a key of 600 segments
  refused by 005-31 at a limit of 100 kB, nothing appended; admitted at
  the release's limit with the limit lowered at the plan, its record
  fails the database at `checkTakeable` (the `Bug`'s message), nothing
  appended, and a restart has the database as before.
  `testLargestActionNextToLargestOldValue` (f): at 200 kB, two cold
  values of 170,000 bytes (the value limit 175,000) and 250 actions of a
  value of 160,000 bytes and 40 small puts: a step carries an old value
  of the largest size beside such an action, every record within
  `recordCap()`, cuts, the values right after a restart.
* **Before and after.** The sustained runs' workload as a probe with the
  hook only (the same seeds; outside the repository), on step 1's jar
  (`c46b0e01`) and on this branch's: on step 1's, 4 and 9 records whose
  set, at the largest node sizes, passed the room of a record with no KVs
  (largest 210,112 bytes at 100 kB, 430,336 at 200 kB), so their take
  rested on the larger cap of a record that carries maintenance and on
  nodes smaller than the largest; the startup pos still moved in every
  window there. On the branch's: none over `dirtyLimit()` (largest 70,912
  and 178,720 bytes), the startup pos moving in every window, the stream
  kept at most 4.88 MB and 17.7 MB as on step 1's (4.81 MB, 18.2 MB). The
  action's 7/8 refused 643 and 496 of the large actions (597 and 426 on
  step 1's). The silent stall itself was the review's RvLong case (below).
* **Bytes.** At the release's limits the cheap test fits every record of
  the stress workloads: StreamDigest quick on the commit of the rule
  (format 8) against step 1's jar: `DIGESTS IDENTICAL (44 of 44)`.
* Tests changed by the action's 7/8: `DbTesterDirtyCount`'s
  `testRefusedAfterKeyTransformations` (the record limit 11,150 bytes for
  its 42 nodes, 10,400 before) and `Reclaim.Tester`'s
  `testLastStepWithinRecordLimit` (220 kB, 200 kB before: its actions
  count up to 902 nodes, 175 kB, and 7/8 of 200 kB is 175,000).

### What is derived and what is assumed

* Derived, by checks in the code: a record's own nodes within
  `dirtyLimit()` by the counts before the go point; no record appended
  whose set, at the largest node sizes, passes `takeRoom()`; so every set
  in D can be taken whole by a later record with no KVs. The step's count
  is from the keys it copies, of any length the Core accepts.
* Assumed, as 005-31 assumes: the counts bound the nodes a transaction
  makes dirty (the walk is proved for puts, 030-29's
  `pe_dirtyNodeBound_puts`, and tested for deletes; the cheap test's
  height is from the stream's length, an argument); a node at a later
  take is at most the largest size counted. Assumed, and checked by
  `checkTakeable` (a failure if not): the nodes that a record's take keeps
  dirty fit in the rest of the record limit (1/16 less 1,712 bytes); none
  of the runs above came near. Assumed, as on `main`: a later record with
  small own bytes comes; under only maximal records the take waits, not
  for good. Assumed for progress: an old KV alone fits `dirtyLimit()`
  when a step meets it (its own transaction was within the action's
  7/8); if not, a part's record with it fails at `checkTakeable`, loudly.
* Not formal (Frans, 14:00 to 14:09): no bound of the record's size is
  derived beyond these checks.

### Long keys (F6)

* The step's count is from the actual keys (`recordDirtyFits`), so any key
  the Core accepts is safe; at the release's limits the cheap test alone
  covers a single key within L3 (8,192 segments: 3 x 42 x 8,192 + 3 nodes,
  about 1.03 M, against 3.7 M at node size 30 and 10.5 M at 8).
* `testLongKeyCopiedByAStep` (f): the review's case, a key of 6,000
  segments under "/#" by `putLongKey` at the release's limits, node size
  8: copied by a commit's step, whose record made more than 5,000 index
  nodes dirty (5,154), within dirtyLimit; the original record cut away;
  the value right after a restart.
* The review's `RvLong` (adapted, appendix 2: `-Dwhen=before|plan|after`)
  on the branch's jar: 3,000 and 7,000 segments at the release's limits,
  the review's lines exactly (copied by a commit's step, 2,581 and 6,009
  index nodes in one record, startup pos 4,240,120 and 7,173,472 of
  4,246,808 and 7,180,160). With the limit of 100 kB from the start: the
  key's transaction refused (005-31, "up to 6003" nodes, 1,154,240 bytes,
  more than 87,500), nothing appended. Lowered at its plan: the database
  fails at `checkTakeable` (5,999 nodes, 1,151,808 bytes, more than
  98,288), nothing appended. Lowered after its record, as the review ran
  it: the startup pos stays at 512, as before; the record was within the
  limit when written, and the limit is a constant outside tests, so this
  case cannot arise but by the test hook.
* `putLongKey` (Trans.Builder, public, "Internal, not API"): BergDB's own
  keys under "/#", longer than L2 up to L3 in a transaction; used by the
  Pub layer's indexes (`IndexManager`, `RwEnvironmentImp`: entries,
  definitions and markers, entries within L6, about 400 bytes) and
  `FormatFuzzer`. Whether the Core bounds them is Frans's (below); the
  Core's acceptance is unchanged.

### The record format (Frans, 14:36)

* `StoredTrans.RECORD_FORMAT` 9; `formatRefused` names release 2026.6 for
  format 8, that this version does not open it and that there is no
  upgrade path. Release 2026.6 refuses format 9 as a newer BergDB's (it
  reads 8 only). Q5 is answered by the record's format; the value node's
  format (5) and the meta block's version (155) are unchanged.
* Tests: `NodeStreamTester.testStartRefusesFormat8` (a start on this
  build's stream with every record's byte 4 set to 8: refused, the
  message names 2026.6, nothing appended); `StoredTrans.testRefusesFormat6`
  refuses 6, 7 and 8. No test built format 8 by hand but through
  `RECORD_FORMAT`.
* StreamDigest has no pinned digests in the code; run quick on the jars
  before and after: all 44 digests change (11 configurations, 4 modes),
  the lengths, first positions and first available positions and times
  identical. The item's sweep reference (`runs/sweep.txt`): the digests
  change, the rest the same (below).
* 027-03: the numbers, and one paragraph on format 9. `releases/next.md`
  has no lines on the format: not changed (step 5, the documents).

### The step reserve (F7; 028-68, B, Frans 16:09)

* `Reclaim.DEFAULT_STEP_RESERVE` for every database. Removed:
  `DbBuilder.reclaimStepReserve` and the system property `stepreserve`.
  The test hook: `DbBuilder.testStepReserve`, package-private as
  `maxNodeSize8()`, given at every start of a test's database (its
  Javadoc); `Reclaim.setStepReserve` package-private. Users in the code:
  `Reclaim.Tester.testStepReserveSplitsSteps` (now at its start and its
  restart) and `DbTesterJavadoc` (its refusal of 0 removed). No script
  passed the property. New: `Reclaim.Tester.testStepReserveIsAConstant`.
  028-68's entry and index row updated (decided, open until it lands).
* The item's probes that set a reserve (`SafetyProbe`, `PubInfoProbe`,
  the review's `RvP1`) call `reclaimStepReserve`: they need
  `testStepReserve` when run again.

### The lock-handover test

`ReclaimMaintainTester.testCommitGoesBeforeTheNextPart` waits for a hook
in the handover, `Db.TestHooks.givingWay()`, called on the call's thread
when its wait for a waiting commit begins (`giveWayToWriters`), and no
longer samples the threads' state, TIMED_WAITING, which a thread that
parks for 20 us and then waits for a core shows only part of the time.
The wait in the handover ends only when the commit has the lock, so the
assertion (the first record after the lock is let go is the commit's)
follows from the hook. The waits' limits (60 s) are hang guards. Run 60
times, six at once: 60 passed.

### Gates

On F53, 2026-11-27, from 16:36, on the branch at `02ad45a0`, then on
`main`'s `dd62fc27`; rebased since onto `a9d87266`, whose new commits
change text only: `java/` and `lean/` at the head are `02ad45a0`'s. The level
scripts each in a copy-on-write copy of the clone, so that their builds
did not meet; load up to 25 while they ran together. Functional runs.

* `java/before-commit.sh`: `BEFORE COMMIT OK (81 s)` (unit 1,733, f 94,
  demos 14).
* `java/stress/level2.sh` (whole, 18 min): `LEVEL 2 OK`. The pins: 144
  files with their hashes. Step 8, treeconf: small 7,240, drain 14,120,
  reclaim 7,545 transactions with 310 touches, as in step 1; 8b, the
  contract and the bridge; 8c, pecmp: 0 differ in the three sets.
* `java/stress/level3.sh` (whole, 16 min): `LEVEL 3 OK`. Step 8, C-STEP 0
  of 23,127 transactions fail, 1,370 STEP lines, 1,042 iterations, 14,954
  old KVs met, 14,679 copies, 23,087 records against their actions; the
  crash set 0 of 5,593, 409 STEP lines, STEP-resume 925 restarts (135
  crashes), 68 iterations across a restart: step 1's figures, one for one.
* `lean/contract/gate.sh`: not run; nothing in `lean/` changed in step 2
  (`git diff` of `lean/` from step 1's head: empty), and step 1's
  `GATE OK` (254 theorems) stands.
* `java/stress/level4.sh quick` (3 min): `LEVEL 4 OK` (its conformance
  with eviction, 18 traces, TRACECHECK OK 18).
* `java/stress/apps.sh quick` (5 min): `APPS OK`.
* The item's probes (`probes/` with appendix 1's change), on the
  branch's jar, 16:46 to 16:59:
  * `sweep.sh`: 27,720 interruptions, 0 different, the start's memory the
    running one's at all; records = accepted actions in all 23 reference
    runs (16,634); 567 torn records continued the same. Against
    `runs/sweep.txt`: the same lengths, records and decided cuts; all 23
    digests differ, by record format 9; the counts "after a physical cut"
    (23,210 against 23,275) and seed 3's physical cut differ, which wait
    for durability.
  * `faults.sh`: `runs/faults.txt` line for line but the six reference
    digests (format 9); bad 0 in all 42 lines.
  * `conc.sh`: ten runs, the replay gave the same stream in all ten.

### For the later steps

* **The pace (F2, F3, F4).** At lowered limits the room cuts many steps
  to their first copy beside large actions (238 of the run above); at the
  release's limits none in the stress workloads. F3's fix (a commit's
  step sized by its allowance, 028-71) makes steps larger, and the room's
  trim is coarse (all, the first copy, none): a larger step that does not
  fit falls to one copy; a trim to the largest prefix that fits (a few
  walks) may be wanted then. F4: `recordDirtyFits` walks under the write
  lock when the cheap test is over (near the action's limit; at lowered
  limits most steps' records); the warm-up before the lock should cover
  the step's paths, which are the walk's too. F2: the charge is of the
  plan as made last, after a trim.
* **The plan made again.** `Reclaim.plan` may run `plan(t, kvs, n)` up to
  three times; each is a function of the stream and the action. The
  exporter reads the final plan (`x.plan`); the statistics of the trims
  (`Stats.roomFirstCopy`, `roomNoStep`) count at the plan, also for an
  action a stop then refuses.
* **028-67's checks** (decided for 2026.7, in the landing) use the
  record header's bytes 5 to 7 under format 9: no conflict with this
  step, which changed byte 4 only.

### Options for Frans

* **O1. BergDB's own long keys in the Core (F6).**
  * (a) As built: the Core accepts them as today, keys under "/#" longer
    than L2 through `Trans.Builder.putLongKey` and `deleteLongKey`, up to
    L3 (56 KiB) in a transaction; the record's room counts them from the
    actual keys. What the Core accepts does not change.
  * (b) `putLongKey` and `deleteLongKey` refuse a key over a bound of
    BergDB's own keys, for example 1 KiB (146 segments), well above the
    Pub layer's largest (about 400 bytes, L6), with an
    `IllegalArgumentException` as L2 does: a new public limit in 024-17.
    The item's arithmetic for the step's last KV (section 3: 60 segments
    assumed) would then hold by a check.
  * Recommended: **(a)**. The record's safety no longer rests on the
    keys' length; (b) changes what the Core API accepts for no case that
    needs it now, and is worth it only if a formal bound of the record is
    wanted later.
* Not an option, a consequence of the reserve (Q3 (b), as the lead
  framed it): 005-31 admits an action within 7/8 of the record limit, no
  longer 15/16. At the release's limits that is 1.879 GB; a transaction
  within L1 to L5 makes at most 1.47 GB dirty by 024-17's count (1.33 GB
  at node size 62), so no transaction within the public limits is refused
  by it (assumed as 024-17 assumes, TP26).

## State

2026-11-27, 20:30, after the review of the landed diff (`review-main.md`).

* **Done:** its R1, R2 with R5, R6 and R7 fixed on the branch
  `031-06-review-fixes`, from `main` at `db92c882`, commit `97954827`
  (each finding's "Fixed" line says how and with what evidence): a `Trans`
  executed again writes the record of a new one with its KVs (R1); the
  take keeps the record's got-dirty set within `takeRoom()` by the count
  that `checkTakeable` uses (R2), and `takeRoom()` counts M4's table (R5);
  the item's probes compile and run on `main`, appendices 1 and 2 applied
  (R6); C-STEP's STEP-action tests one operation a key in every record
  (R7); Db's class comment no longer names 2026.6's filler. Gates on the
  branch, F53, functional runs with other work on the machine:
  before-commit.sh `BEFORE COMMIT OK (71 s)`; level2.sh `LEVEL 2 OK`
  (16 min; treeconf and pecmp's figures of step 2); level3.sh
  `LEVEL 3 OK` (15 min; C-STEP's figures of step 2 one for one, its fault
  test 24 faults, `twice` new); StreamDigest quick against `db92c882`'s
  jar `DIGESTS IDENTICAL (44 of 44)`; `probes/sweep.sh` 27,720
  interruptions, 0 different, 567 torn records, 0 different; `faults.sh`
  and `conc.sh` as at step 2; the review's `RmReuseProbe` 20 of 20 the
  same, `RmRoomProbe` 9 of 9 without a failure, its sweep at lowered
  limits 12,105 interruptions and 2,142 torn records, 0 different.
  `lean/contract/` unchanged: `gate.sh` not run.
* **Not done:** R3 and R4 (the lead's to register); F2 to F4 (step 3); the
  kept times (Q4); 028-67's checks (C1, C3); the documents (step 5: 027,
  027-02 beyond STEP-action's one operation a key, 027-13's C-STEP rules,
  the full description of format 9, the Javadoc of `maintain(budget)`);
  night.sh, week.sh, level4.sh, timing.sh on the branch.
* **For Frans:** O1, in step 2's options, as at 17:05.
* **Next:** the lead's review and landing of `031-06-review-fixes`.

Earlier, 2026-11-27, 17:05.

* **Done:** steps 0 and 1 (above), and step 2: the record's room by a
  check (F5) with the step's count from the actual keys (F6), record
  format 9 for Frans's decision of 14:36, the step reserve a constant
  (F7; 028-68, B), the handover test without a sampled thread state;
  027-03 and 027-08 where they state the format's number and the index
  limits. Gates: before-commit.sh, level2.sh and level3.sh whole,
  level4.sh quick, apps.sh quick, the item's sweep, faults and conc; no
  change in `lean/`.
* **Not done:** the item's text and `probes/` (the lead's; the probes need
  appendix 1's change, `SafetyProbe`, `PubInfoProbe` and `RvP1`
  `testStepReserve`, `RvLong` appendix 2's); F2 to F4 (step 3); the kept
  times (Q4); 028-67's checks (C1, C3); the documents (step 5: 027, 027-02,
  027-13's C-STEP rules, the full description of format 9, the Javadoc of
  `maintain(budget)`); night.sh, week.sh, level4.sh whole, timing.sh.
* **For Frans:** O1 (BergDB's own long keys in the Core), in step 2's
  options; recommended (a), as built.
* **Next:** the lead's review of the branch `031-06-landing`; the merge
  into `main` (`--no-ff`) when Frans's two points of section 9 are
  settled; step 3 on `main`.

## Appendix: the probes for the test hook

The change of the item's probes (at `fa11d15f`) for `Db.TestHooks.maintainMaxParts()`, as the
gate of step 0 ran them:

```diff
--- probes/P2CrashProbe.java
+++ probes/P2CrashProbe.java
@@ -1,6 +1,5 @@
 package bergdb.core;
 
-import java.lang.reflect.Method;
 import java.security.MessageDigest;
 import java.util.*;
 import java.util.concurrent.atomic.AtomicLong;
@@ -29,7 +28,7 @@
  *   stop:     stopped there (transExecuted calls stop());
  * then a start from the stream, and the actions after record k's: the next action after
  * it, or for a part of a call that wrote p parts, the reference with that call ended after
- * p parts (Db.maintain(int, int)) and the action after the call. -Drestart=N restarts the
+ * p parts (Db.maintain(int) with Db.TestHooks.maintainMaxParts()) and the action after the call. -Drestart=N restarts the
  * continued database every N actions too. The continued stream must equal the reference:
  * the same length, the same decided cut, and the same bytes from the first position kept.
  *
@@ -66,7 +65,8 @@
     static final String CLOCK = System.getProperty("clock", "");
     static final boolean EVICT = Integer.getInteger("evict", 0) == 1;
     static long refusedCalls;
-    static Method maintainParts;
+    /** The most parts that write of the next maintain() call (Db.TestHooks.maintainMaxParts). */
+    static volatile int maxParts = Integer.MAX_VALUE;
 
     static final class Action {
         char kind;          // 'p' put(s), 'd' delete, 'e' empty, 'm' maintain, 's' sd, 'r' retain
@@ -188,7 +188,12 @@
             case 'r': d.setRetainDuration(a.arg * SEC); break;
             case 'm':
                 if (a.arg < 0) {
-                    maintainParts.invoke(d, B, -a.arg - 1);
+                    maxParts = -a.arg - 1;
+                    try {
+                        d.maintain(B);
+                    } finally {
+                        maxParts = Integer.MAX_VALUE;
+                    }
                 } else {
                     d.maintain(a.arg);
                 }
@@ -200,15 +205,6 @@
             return false;
         } catch (bergdb.storage.StreamIoException e) {
             return false;
-        } catch (java.lang.reflect.InvocationTargetException e) {
-            Throwable c = e.getCause();
-            if (c instanceof Crash || c instanceof DbStoppingException || c instanceof DbFailedException
-                    || c instanceof bergdb.storage.StreamIoException) {
-                return false;
-            }
-            throw new RuntimeException(c);
-        } catch (IllegalAccessException e) {
-            throw new RuntimeException(e);
         }
     }
 
@@ -224,6 +220,9 @@
 
     static void installHook() {
         Db.testHooks = new Db.TestHooks() {
+            public int maintainMaxParts() {
+                return maxParts;
+            }
             public void beforeApply(Db.ExecuteData x) {
                 if (countOn && mode.equals("pre") && records + 1 == stopAt) {
                     records++;
@@ -349,8 +348,6 @@
         int n = Integer.parseInt(args[1]);
         int sd = Integer.parseInt(args[2]);
         String modes = args.length > 3 ? args[3] : "all";
-        maintainParts = Db.class.getDeclaredMethod("maintain", int.class, int.class);
-        maintainParts.setAccessible(true);
         installHook();
         List<Action> as = workload(seed, n, sd);
         List<Rec> rs = new ArrayList<>();
--- probes/FaultProbe.java
+++ probes/FaultProbe.java
@@ -66,6 +66,9 @@
     static void installHook() {
         Db.testHooks = new Db.TestHooks() {
             boolean first;
+            public int maintainMaxParts() {
+                return P2CrashProbe.maxParts;
+            }
             public void beforePlan(Db.ExecuteData x) {
                 if (!P2CrashProbe.countOn) return;
                 first = true;
@@ -147,8 +150,6 @@
         int n = Integer.parseInt(args[1]);
         int sd = Integer.parseInt(args[2]);
         int perKind = args.length > 3 ? Integer.parseInt(args[3]) : 6;
-        P2CrashProbe.maintainParts = Db.class.getDeclaredMethod("maintain", int.class, int.class);
-        P2CrashProbe.maintainParts.setAccessible(true);
         installHook();
         List<P2CrashProbe.Action> as = P2CrashProbe.workload(seed, n, sd);
         List<P2CrashProbe.Rec> rs = new ArrayList<>();
--- probes/ConcProbe.java
+++ probes/ConcProbe.java
@@ -1,6 +1,5 @@
 package bergdb.core;
 
-import java.lang.reflect.Method;
 import java.util.*;
 import java.util.concurrent.atomic.AtomicLong;
 
@@ -18,7 +17,7 @@
  * records after them), on a clock that the threads move on together. Every record is
  * logged, in the order the write lock gave, with the action that wrote it and its time.
  * Then one thread replays the logged actions, each at its record's time (a part as
- * maintain(B, 1): the call's first part that writes, which is the part due), on a new
+ * maintain(B) with Db.TestHooks.maintainMaxParts() 1: the call's first part that writes, which is the part due), on a new
  * database: the stream must be the same, byte for byte from the decided cut, its length and
  * its decided cut the same. So the stream is a function of the accepted actions, in the
  * write lock's order, with their times, whatever the threads did.
@@ -158,8 +157,14 @@
         Db d2 = start(s2, node);
         d2.setStartupDistance(2000);
         d2.setRetainDuration(SEC);
-        Method mp = Db.class.getDeclaredMethod("maintain", int.class, int.class);
-        mp.setAccessible(true);
+        // A part as maintain(B) with at most one part that writes (Db.TestHooks.maintainMaxParts).
+        Db.testHooks = new Db.TestHooks() {
+            public int maintainMaxParts() { return 1; }
+            public void transExecuted(Db.ExecuteData x) {}
+            public void valueNodeCreated(ValueNode node, long[] key) {}
+            public void nodeTouched(Node node) {}
+            public void nodeReplaced(Node node) {}
+        };
         int parts = 0, commits = 0, setters = 0;
         for (Object[] e : log) {
             char kind = (Character) e[0];
@@ -176,7 +181,7 @@
                 commits++;
                 break;
             }
-            case 'm': mp.invoke(d2, (Integer) e[2], 1); parts++; break;
+            case 'm': d2.maintain((Integer) e[2]); parts++; break;
             case 'r': d2.setRetainDuration((Long) e[2]); setters++; break;
             case 's': d2.setStartupDistance((Integer) e[2]); setters++; break;
             default: throw new IllegalStateException();
@@ -185,6 +190,7 @@
         d2.sync(SyncLevel.ORDINARY);
         final long decided2 = d2.getFirstAvailablePos();
         d2.close();
+        Db.testHooks = null;
         P2CrashProbe.Image b = P2CrashProbe.image(s2, decided2);
         String why = P2CrashProbe.compare(a, b);
         System.out.println("seed " + seed + ", " + seconds + " s, " + writers + " writers, node "
```

## Appendix 2: RvLong for step 2

The change of the review's probe (`review-probes/RvLong.java` on `main`)
that step 2 ran, with `-Dwhen=before|plan|after` for when the lowered
record limit takes effect:

```diff
--- review-probes/RvLong.java
+++ review-probes/RvLong.java
@@ -14,8 +14,16 @@
  * Usage: java -ea -cp OUT:JAR bergdb.core.RvLong SEGMENTS [NODE]
  *   -Dlimit=N: a lowered record limit (StoredTrans.recordLimit), to see what follows when a
  *   record's dirty set passes the room of every later record (F5's consequence).
+ *   -Dwhen=after (the default): the limit lowered after the key's record, as the review ran
+ *   it; before: in force from the start, as a limit is in production; plan: lowered after the
+ *   key's transaction is admitted, before its plan (031-06's landing, step 2: the key's
+ *   transaction is refused by 005-31 with before, and with plan its record is not written:
+ *   Db.checkTakeable fails the database).
  */
 public class RvLong {
+    static long s0(Db db) {
+        try { return db.getStreamLength(); } catch (Throwable e) { return -1; }
+    }
     public static void main(String[] args) throws Exception {
         final long SEC = Clock.UNITS_PER_SEC;
         int segments = Integer.parseInt(args[0]);
@@ -35,10 +43,38 @@
         Random r = new Random(1);
         byte[] v = new byte[100];
         r.nextBytes(v);
-        db.execute(db.trans().putLongKey(key, null, v, null).build());
+        final String when = System.getProperty("when", "after");
+        final long limit = Long.getLong("limit", 0);
+        if (limit > 0 && when.equals("before")) StoredTrans.recordLimit = limit;
+        if (limit > 0 && when.equals("plan")) {
+            Db.testHooks = new Db.TestHooks() {
+                public void beforePlan(Db.ExecuteData x) { StoredTrans.recordLimit = limit; }
+                public void transExecuted(Db.ExecuteData x) {}
+                public void valueNodeCreated(bergdb.dag.ValueNode node, long[] key) {}
+                public void nodeTouched(bergdb.dag.Node node) {}
+                public void nodeReplaced(bergdb.dag.Node node) {}
+            };
+        }
+        final long length0 = db.getStreamLength();
+        try {
+            db.execute(db.trans().putLongKey(key, null, v, null).build());
+        } catch (Throwable e) {
+            Db.testHooks = null;
+            Throwable c = e;
+            while (c.getCause() != null) c = c.getCause();
+            System.out.println("RvLong: a key of " + key.length + " segments (" + Trans.keyBytes(key)
+                    + " bytes) under \"/#\", the record limit " + limit + " " + when + ": "
+                    + (e instanceof bergdb.pub.util.DbException ? "refused" : "failed") + ", "
+                    + e.getClass().getSimpleName() + (c != e ? " (" + c.getClass().getSimpleName() + ")" : "")
+                    + ": " + c.getMessage() + "; the stream's length " + length0 + " before, " + s0(db) + " after");
+            try { db.close(); } catch (Throwable x) {}
+            StoredTrans.recordLimit = saved;
+            return;
+        }
+        Db.testHooks = null;
         // The limit is lowered after the key is in the stream: its own transaction is
         // admitted by the release's limit, as a transaction near that limit would be.
-        if (Long.getLong("limit", 0) > 0) StoredTrans.recordLimit = Long.getLong("limit");
+        if (limit > 0 && when.equals("after")) StoredTrans.recordLimit = limit;
         Reclaim.Stats stats = db.internal().reclaim().enableStats();
         long copies = 0, maxRecord = 0, maxDirtied = 0;
         boolean copied = false;
```
