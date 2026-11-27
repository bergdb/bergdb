# 031-06. Review of the landed diff

2026-11-27, from 18:20, by an agent of lead-1127 on Fable, in a clone of
`main` outside the repository (branch `031-06-review-main`, from
`5b88cc80`). Reviewed: the merge `5b88cc80`, "Merge 031-06: one record an
action", as `git diff 5b88cc80^1 5b88cc80` of `java/` and `lean/`: the
landing's steps 0 to 2 (readme, section 9). The merge's tree is its
branch's head (`5605e9c2`): the first parent is the merge base, so
nothing of `main` was mixed in.

Independent of the review of the prototype: sections 1 to 6 were written
before `review-fable.md` was read; section 7 compares.

The probes are in `review-main-probes/`, with their runs in
`review-main-probes/runs/`; `review-main-probes/run.sh` says how each was
run. On F53, functional runs, other work on the machine.


## 1. Result

* **The bytes.** No restart, stop, failure, torn record or eviction
  schedule that the probes tried changed a byte against the same actions
  run without it, also where the record's room plans a step again
  (section 4). One thing outside the stream and the action does change
  the bytes: fields that a failed execution leaves on a `Trans` (R1).
* **The record's room.** The check before the append
  (`Db.checkTakeable`) fails databases at lowered record limits under
  plain workloads, in a commit of one small put and in a part of
  `maintain()` (R2). At the release's limits the same arithmetic is far
  from the limit; that distance is argued, not derived.
* **A start writes nothing** besides recovery's completion of a torn
  record and of a cut meta block, as before; no record is appended
  between two actions; a part with nothing due appends nothing.
* `java/before-commit.sh` on the clone at `5b88cc80`: `BEFORE COMMIT OK
  (65 s)`.


## 2. Findings, ranked

### R1. A Trans executed again after a failure writes other bytes (medium)

* **Where.** `Db.executeLocked`, `java/src/bergdb/core/Db.java`, lines
  3068 to 3078 and 3125 to 3130. The fields of the plan's record
  (`Trans.touch`, `touchCount`, `touchOldBefore`, `maintainTakeTo`,
  `recordCap`, and the reset of `dirtiedNodes` and `dirtiedBytes`) are
  set only when the execution has a plan, and cleared only after a
  record that worked. An execution that fails the database after its go
  point (line 3133, `fail`) leaves them on the user's `Trans`.
* **What happens.** `Trans`'s Javadoc allows a `Trans` to be executed
  again, and `Trans.testTransReuse` does so on a database started after a
  close. Executed again when its record carries no plan, the `Trans` that
  failed still has `touch` true: `Db.putKvs` (line 3872) runs
  `touchPaths`, whose branch without a plan (line 4293, "a test's
  touch") makes dirty the paths of the transaction's own keys before the
  batch, and `endOfTrans` then keeps the nodes that the batch replaces in
  the got-dirty list. The record's got-dirty list, and so the stream,
  differs from that of a new `Trans` with the same KVs at the same time.
  At a lowered record limit the stale `recordCap` changes the take's room
  as well.
* **A scenario.** A commit whose record carries a step fails the
  database (a storage error at the append, an Error); the application
  starts the database again; another thread's commit takes the step that
  was due; the first thread executes its `Trans` object again. Its record
  is not the one that a new `Trans` of the same contents gives: the
  stream depends on memory that is neither the stream nor the action
  (010-01, P2).
* **Shown.** `review-main-probes/RmReuseProbe.java`: a database failed by
  the test hook in a commit that carries a step, before its append or
  after it; on two copies of the stream, a commit of another key, then
  the action again, with the `Trans` that failed and with a new one of
  the same KVs. 20 runs (5 seeds, node sizes 8 and 30, both points): **16
  gave different streams**, 4 the same; the control, the failed `Trans`
  with the five fields cleared by hand, gave the new `Trans`'s stream in
  all 20 (`runs/reuse.txt`).
* **Why the probes of the item did not meet it.** `P2CrashProbe` and
  `FaultProbe` build a new `Trans` for every execution.
* **A fix.** These fields are the record's, not the transaction's: keep
  them in `Db.ExecuteData` (`x.plan` is there already: `touch` is
  `x.plan != null && x.plan.touchKeys != null`, the take's target
  `x.plan.takeTo`, the cap a function of `x.plan != null`), or set all of
  them at every execution, whatever the plan. The first removes four
  fields from `Trans` and the "set again, cleared after" pair; a test's
  touch (`DbTester`) then needs its own switch.

### R2. The check before the append fails databases at lowered limits (medium for the tests, none found at the release's limits)

* **Where.** `Db.checkTakeable` (`Db.java`, line 3673) against
  `StoredTrans.takeRoom()` (`StoredTrans.java`, line 152); the take's
  room in `Db.store` (line 3711, `cap`, and line 3724, `takeTo`);
  `StoredTrans.recordCap()` (line 190); `Reclaim.MAINTAIN_TAKE_BYTES`
  (`Reclaim.java`, line 818).
* **The rule's gap.** The counts before the go point bound the record's
  own index nodes (15/16). The got-dirty set also holds the nodes that
  the record's take writes and keeps dirty (`handleStillDirtyNodes`), and
  nothing bounds those but the bytes the take may write, counted at their
  actual sizes: the rest of the record's cap. `checkTakeable` counts them
  at the largest node size (a node in D may still grow). So a take of
  nodes smaller than the largest, many of them kept dirty, gives a set
  over `takeRoom()` with every count before the go point within its
  limit. Two things widen it at a lowered limit: a
  record that carries maintenance has `recordCap()`, 455,894 bytes at a
  limit of 100,000, as its take's room; and M4's take adds 256 KiB
  whatever the limit.
* **Shown.** `review-main-probes/RmRoomProbe.java`, `room.sh`
  (`runs/room.txt`): single puts of 30 bytes at random among 20,000 keys
  of three segments, R = 1 s.
  * Record limit 100 kB, node size 8, startup distance 2 MB, one
    `maintain(100000)` after 30,000 commits: the database fails in a part
    ("641 of them, may take 123712 bytes, more than a later record can
    take, 98288").
  * The same without any `maintain()` call, a value of 80 kB every 200th
    commit: the database fails in a commit of one put of 30 bytes whose
    record carried maintenance (523 nodes, 101,696 bytes).
  * Record limit 200 kB at node size 30, the default, startup distance
    4 MB: fails in a part (372 nodes, 202,368 bytes against 198,288).
  * With `ReclaimRoomTester`'s startup distance, 20,000 bytes: no
    failure, the largest set 202 nodes. The item's evidence for the rule
    (landing, step 2: the sustained runs, "none of the runs above came
    near") is at startup distances below the record limit.
* **At the release's limits.** `takeRoom()` is about 3.9 million nodes
  at node size 30, and `recordCap()` is the record limit. A record would
  have to write that many index nodes and keep most of them dirty; with
  a startup distance of at most 10^9 the nodes kept dirty are inner
  nodes of a section of a few GB. Not reached by any run here; an
  argument, not a bound. The landing states the same as an assumption
  ("checked by `checkTakeable`"); what is new is that the assumption
  fails where the tests lower the limit and the startup distance is
  larger than it.
* **What it costs today.** Only databases with `StoredTrans.recordLimit`
  lowered: the unit and f-tests and the item's probes (`SafetyProbe` at
  100 kB to 1 MB). A later test at a lowered limit with a larger startup
  distance fails by this check, not by a fault of what it tests.
* **A fix.** Bound the take by the same count as the check, so that the
  check cannot fail by it: stop the take (`TransSeq.take` and `takeTo`)
  before the transaction whose nodes, each at the largest size with its
  entry, would bring the record's got-dirty set over `takeRoom()`,
  counting every taken node as kept dirty. A deterministic count, no
  effect at the release's limits. And at a lowered limit give M4's take
  and `recordCap()` no more than the record limit allows a set to be.

### R3. One small put, then maintain(): the whole live data again (low: the cost of a decided rule)

* **Where.** `Reclaim.passDue` (`Reclaim.java`, line 903), M1 of
  `planPart`: a pass begins when the stream kept holds a record of the
  application's; 031-04's direction ("No drain, no MIN_RELEASE"), which
  this merge brings to `main`.
* **Measured.** `review-main-probes/RmPassProbe.java` (`runs/pass.txt`),
  at the release's limits: a database brought to rest by `maintain()`
  calls, one put of 1 byte, calls until five in a row write nothing.
  20,000 keys of 100 bytes: the put's record 568 bytes, the calls then
  wrote 4.43 MB; the stream kept 4.36 MB before and 4.38 MB after.
  100,000 keys of 200 bytes: 31.9 MB written for a record of 576 bytes.
  Until this merge a call began an iteration only if its cut released
  400 kB (028-51, 028-62).
* Not a fault of one record an action. For the pace (step 3): an
  application that writes a little and calls `maintain(budget)` when
  idle rewrites its live data once a retain duration.

### R4. takeRoom() counts a taker with no KVs; M4's record has one (low, by reading)

* `StoredTrans.takeRoom()`'s Javadoc names "an empty commit, a part's
  take, M4" as records with no KVs. M4's record stores the table
  (`Reclaim.planPart`, lines 870 to 872), so at the release's limits,
  where `recordCap()` is the record limit, its room is `takeRoom()` less
  the table's value node and the entries of its path. A set within those
  bytes of `takeRoom()`, at actual sizes, is taken by an empty commit of
  the application's only; M4's parts would each append a table record
  and not move the startup pos, as many as a call's budget pays for.
  The window is a few kB in 2 GB; no run comes near. With R2's fix the
  count can use M4's room.

### R5. The item's probes do not run on main (low: the evidence cannot be run again as committed)

* `probes/SafetyProbe.java`, `probes/PubInfoProbe.java` and
  `review-probes/RvP1.java` do not compile on `5b88cc80`
  (`DbBuilder.reclaimStepReserve` is gone, 028-68);
  `probes/P2CrashProbe.java`, `FaultProbe.java` and `ConcProbe.java`
  compile and fail at their start (`Db.maintain(int, int)` by
  reflection, gone in step 0). The change is `landing.md`'s appendix,
  not applied to the files. `review-main-probes/P2CrashProbe.java` is the
  item's with that appendix applied and this review's variants.

### R6. One operation a key is tested in a step's record only (low)

* The contract's `MaintenanceOK` (`lean/contract/Contract/
  ReclaimValues.lean`, line 47) takes one operation a key in every
  record. C-STEP tests it per STEP line (`lean/Check/Steps.lean`, line
  998, in `reclaimStepFailures`); `actionFailures`, which runs on every
  record, does not: a record without a step that held its action's put
  and a second operation at the same key would pass STEP-action. Java
  cannot write one today (`Db.transformKeys` refuses the action,
  `Db.merge` fails the database), so nothing is wrong in a trace; the
  check is one line in `actionFailures`, and a fault for
  `step-faults.sh`.


## 3. The record-room arithmetic

* `dirtyLimit()` 15/16, `actionDirtyLimit()` 7/8, `stepDirtyRoom()` 1/16
  and `takeRoom()` (the limit less 48 and `TOP_BYTES`) are as the landing
  states them. The 1/16 between `dirtyLimit()` and `takeRoom()` is said
  to hold the nodes that the take keeps dirty; nothing ties the take to
  it (R2).
* At a lowered limit a record that carries maintenance may be several
  times the record limit (`recordCap()` adds a value node of up to
  `valueLimit()`, 256 kB and 1/16), where at the release's limits it is
  the limit itself. The tests at lowered limits so run a rule, room on
  top, that the release does not have; the release rests on L1 to L5
  being far below the limit. A lowered-limit test of the release's rule
  would give a record with maintenance the record limit, and the action
  the limit less the step's room (the readme's Q3 (b)).
* `Db.recordDirtyFits` gives the walk the action's keys and then the
  plan's, not merged in key order; `Dag.dirtyNodeBound` counts by node,
  so the order does not change the count. The action's KVs are counted
  with their values after the transformations (a transformation that
  gave null is a delete, 20 a level), as its Javadoc says.
* A step that fits beside no action is left out of every commit's
  record, and a part's keeps it and may fail at `checkTakeable`. For that
  an old KV with the row must pass `dirtyLimit()` by the count: at the
  release's limits a key of 8,192 segments counts about 0.9 million
  nodes at a stream of 1 TB (a height of 36), against 3.7 million at
  node size 30; so only at lowered limits. Beside an action near its
  limit such a key waits for a smaller action.
* Under a commit near the action's limit the plan runs up to three
  times, each with its scan, and `recordDirtyFits` walks all the
  record's keys up to twice more, under the write lock (the landing's
  note for F4).


## 4. What was checked and found right

* **Restarts, stops, failures and torn records where the room plans
  again.** `review-main-probes/P2CrashProbe.java` and `sweep-rm.sh`: the
  item's probe with a lowered record limit (`-Dlimit`), actions of 2 to
  200 keys (`-Dbig`), split steps (`-Dreserve`), value transformations
  that read the value before, some giving a delete (`-Dxform`), keys of
  14 segments (`-Ddeep`), and torn records of parts and setters too
  (`-Dtornall`). The results are in section 4.1.
* **What a plan reads.** By reading `Reclaim.plan`, `planCommit`,
  `planPart`, `planStep`, `planSafe`, `planCut` and what they call: the
  table's rows, a, the first available position, the settings, the
  stream's length, the last record's time (`DbClock.lookupTime`, which a
  reader's `currentTime()` does not move), the record's own time, the
  startup pos, the last valid meta block's transaction, the tree, and
  the action's KVs after their transformations. The scan's reserve
  counts index nodes by id (`NodeCollection.MaintenanceFollower`), a
  step's values by their stream positions; neither depends on what is
  resident. The physical cut and the durable length are read by no plan.
  `maintain()`'s time charge (the dead hand) comes only after the last
  part that writes.
* **The meta block.** A start sets the block's last transaction to the
  stream's last committed record (`Db.getStartupPosFromLastTransaction`),
  and recovery's blocks name what the last valid one named, so the cut's
  wait for a meta block reads the same after a start.
* **a.** After the creating start and after a restart of that stream a
  is the same (272; a probe of ten lines, not kept).
* **The setters.** `setStartupDistance` sets its field before its
  record and restores it if the commit throws; `setSettings` sets after.
  Both under the write lock.
* **One operation a key.** `Reclaim.finishPlan` and `Db.merge` use one
  order (`Keys.compareArrays`), which is the order of `Trans.Builder`'s
  sort and of `sortByKey`.
* **The Lean checks.** `STEP-puts` takes any operation at the key as a
  write, a no-op delete (`OP N`) too; `treecheck`'s C-T3 checks that an
  `OP N` is a no-op of the model, so an old KV met cannot pass by one
  where both checkers run. The contract's weaker `StepTx` (every old KV
  met written by the record) is what Java does: the action's put makes
  a value node after pCut, its delete leaves none. No gate of `lean/`
  was run again here: the merge's `lean/` is the branch's, which the
  landing gated. One gap is R6.

### 4.1. The sweep's results

(Filled in from `runs/sweep-rm.txt`.)


## 5. Simplicity and clean-up

* The plan's fields on `Trans` (R1): into `ExecuteData`.
* `RecordPlan.finish()` through the row's and the table's value
  transformations in `Db.putKvs`: the row's `rewritten` is patched from
  `Trans.dirtiedBytes` by whichever transformation runs first, and
  `apply()` calls it once more. The fixed-width patch of step 3 replaces
  it; until then it is the least direct path in the change.
* `Reclaim.plan` plans from the start up to three times. A step planned
  once, with the scan's result trimmed to the copies that fit, would
  scan once.
* `Db.store` writes the sum of the record's bytes twice (lines 3701 to
  3707 before the take, 3717 to 3723 before M4's), and `Db.maintain` has
  the handover and the pending cut twice.
* Comments that describe what is gone: `Db.putKvs` (line 3896, "Reclaim.
  step adds those of the nodes that the batch makes dirty after it ...
  and stores the row again"); `Reclaim.initFromDb` (line 1315, "and
  again after it"); `Trans.touch`'s Javadoc ("For internal transactions
  of reclaim, its steps"); `Reclaim`'s class comment of 2013
  (`transactionCompleted`); `Reclaim.recordWritten` (line 1501) counts a
  part's step by `t.touch`; `StoredTrans.takeRoom()`'s "M4" (R4).
* Which records carry maintenance is told by three flags of `Trans`
  (`isInternal`, `part`, `noMaintenance`; `Db.planMaintenance`, line
  3148): one kind (a commit, a setter, a part, BergDB's own) would say
  it. `Maintenance.Plan` holds reclaim's statistics types
  (`Reclaim.TouchCount`, `touchOldBefore`), which the boundary need not
  know.
* `Reclaim.cutIfDurableNow()` only calls `cutIfDurable()`;
  `IterationTable.serialize()` has no caller.
* The probes of the item (R5).


## 6. Not done

* `night.sh`, `week.sh`, `timing.sh`, the level scripts and
  `lean/contract/gate.sh` were not run again.
* The Pub layer's index jobs, the trace exporter and the contract's
  proofs were read for what the diff changed, not reviewed as a whole.
* No run at the release's limits with records near them.


## 7. Against the review of the prototype

`review-fable.md` (13:10 to 14:30, on the prototype's `fa11d15f`), read
after sections 1 to 6 were written and committed (`44bc504f` of the
review's branch).

* **New here, all six.**
  * R1: that review ran "a Trans executed again" among `RvFront`'s
    actions and compared the values read, on a database that did not
    fail; the fields left by a failed execution, and the bytes, are new.
  * R2: its F5 was the missing check (a dirty set over the room stalls
    the take with no failure). Step 2 built the check; R2 is that the
    check fails where the take, not the counts before the go point, fills
    the set. The stall of F5 is not reached silently any more: a set
    within `takeRoom()` is taken by a record with no KVs.
  * R3 is of 031-04's rule, which the prototype had; that review measured
    the pace of commits (F2, F3), not a call after one put.
  * R4, R5 and R6 are of code and files that came with the landing.
* **Its findings, as the landed diff has them** (read; F1 and F7 also
  ran in the landing's gates, not again here):
  * F1, the conformance: built (step 1). R6 is a gap in what it tests.
  * F2, F3, F4, the pace and P1: not built (step 3); nothing here.
  * F5, the admission: built as a count of the record and a check before
    the append (step 2); R2 and R4.
  * F6, long keys: the count is from the actual keys
    (`Db.recordDirtyFits`); O1 is open.
  * F7, the step reserve: a constant with a test hook (028-68, B); no
    builder setting or system property of it is left in `java/src`.
  * F8, the Pub layer's jobs that commit by themselves: as it was; not
    in this diff.
  * F9, `Db.getTrans` gives a commit's record with reclaim's copies, row
    and table: as it was; `StoredValueNode.isCopy()` tells the copies.
