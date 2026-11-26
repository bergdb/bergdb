# 031-05. Every write a function of the stream and the user actions

Created 2026-11-26 by Frans Lundberg. Status: open.

A study of a goal Frans set on 2026-11-26: that every write to the stream
is a function of the stream itself and the sequence of user actions. It
answers 028-54 (a stop or a crash inside a commit's maintenance changes
the stream) and builds on 031-04 (`maintain(budget)`) and its prototype.


## 1. The question

On `main` and on 031-04's prototype, a commit's maintenance runs after
the user record, in the same call, triggered by an event in memory (the
transaction completed). A crash or a `stop()` between the user record and
reclaim's records after it makes the next commit do other work at other
positions: the stream differs from the uninterrupted run's from that
record on (028-54; `MidCallProbe` of 031-01; Codex's review of 031-04,
finding 7). The Lean model proves the writer deterministic for a given
list of transactions, with restarts after any transaction of the list
(lean/SIS/ReclaimTheorems.lean, `T12_restartCut`), but which internal
transactions Java's policy chooses is outside the model.


## 2. The decision

Frans decided on 2026-11-26:

* The goal is that every write to the stream is a function of the stream
  itself and of the sequence of user actions.
* A user action is an accepted call of `Db.execute()` or `Db.maintain()`,
  with its time; accepted means that the call does not throw.
* The user actions are then like functions without side effects: input
  the user actions, output the stream.
* This extends P2 (010-01: the stream a function of the accepted
  transactions, a restart insertable between any two transactions without
  changing the bytes; Frans's goal of 2015-12-28) to maintenance and to
  anything that writes.
* It is to be worded precisely and, when possible, proved.
* 010 is not edited (only Frans edits the principles); this study
  proposes a wording.

This answers 028-54's question: P2's "between any two transactions" is to
cover a restart, a stop and a crash between a user record and the
internal records after it, and inside a `maintain()` call.


## 3. The plan

By an agent of lead-1126, in the clone c315 (branch `031-05`, from c314's
`031-04` at `cfb195f3`).

1. **The invariant**: a precise statement; a draft wording for P2's
   extension; what "accepted", "a function of" and "after a crash" mean;
   a crash inside an action.
2. **An inventory** of every code path that writes to the stream, with
   its inputs: which are in the stream or the action, which are not
   (memory, the wall clock, thread timing), and how each that is not could
   be made so.
3. **A prototype** on 031-04's: the commit's maintenance moved to the
   start of the next write, as the stream says it is due, from inputs in
   the stream only.
4. **Evidence**: crashes and stops at every record boundary, inside
   commits and inside `maintain()` calls, the continued stream compared
   with the uninterrupted one; StreamDigest and RestartInvariance;
   `HoleProbe` and `IdleLiveProbe` as in 031-04; `before-commit.sh`; the
   costs.
5. **A sketch of the Lean statement**: the policy as a function of the
   stream, and P2 with crashes as a theorem; what in lean/ would change.
6. **Open questions** for Frans, with recommendations.

The results are in sections 4 to 11. The prototype's code is
`prototype.diff`, its probes are in `probes/`.


## 4. The invariant

Written 2026-11-26 by an agent of lead-1126. A proposal: 010 is Frans's.

### 4.1. The terms

* **An action** is a call of the database by the application that may
  write to the stream:
  * `Db.execute()`, with its transaction;
  * `Db.maintain(budget)`;
  * the setters that commit a record: `setStartupDistance`,
    `setRetainDuration` and `setReclaimInternalFraction`. They are not
    `execute()` or `maintain()`, but they are transactions in P2's sense
    today, and the wording names them.
  * The Pub layer's calls reach the Core through these.
* **Its time** is the database time that the action gets: for a
  transaction, its record's time; for a `maintain()` call, the time that a
  transaction beginning then would get (`DbClock.actionTime` in the
  prototype). It is an input, as the transaction's contents are. A reader's
  `currentTime()` can move it by a few units (`DbClock.lastReadTime`), and
  so can the clock; neither matters once the time is taken as given.
* **Accepted.**
  * A call that returns is accepted. One that throws is not, and writes
    nothing of its own.
  * After a crash, a `stop()` or a failure (P7) inside the call: an
    `execute()` or a setter is accepted if its own record is in the stream
    at the next start (`execute()`'s Javadoc: "whether this transaction is
    in the stream is known after the restart").
  * A `maintain(b)` call that a crash or a stop interrupts counts as
    accepted, as the same call with a smaller budget: one that ends after
    the parts it wrote.
  * A `maintain()` call that hands the write lock to a commit between two
    of its parts (031-04's Q9) counts as two calls, before and after the
    commit, with the same time.
* **Maintenance due** is what the stream says the database is to write
  before the next action's own records: on `main`, the internal records
  that follow a user record in the same call.
* **A crash** stops the process at any point. The stream then holds whole
  records up to some record boundary (recovery completes or drops a torn
  tail, 014-01; 035-01). **A stop** is `stop()`, from any thread, at any
  point. **A restart** is a start from the stream that a crash, a stop or a
  close left.

### 4.2. The statement

For every sequence of accepted actions A1 to An, each with its time, there
is one stream S(A1 .. An) such that:

1. **Without interruptions**, the stream after An's call is S(A1 .. An)
   or, with the deferred design (D1, section 6.2), S(A1 .. An) without the
   maintenance due after An.
2. **With interruptions**: whatever crashes, stops and restarts come
   between and inside the calls, whatever refused calls come between
   them, and whatever the timing, the threads and the cache, the stream
   after a crash, a stop or a restart is a prefix of S(A1 .. An), A1 to An
   the actions accepted until then, ending at a record boundary.
3. **It continues**: S(A1 .. An) is a prefix of S(A1 .. An, A(n+1)), and
   the next accepted action's call writes, before its own records, the
   maintenance that the stream says is due.

S is defined by a writer that is a function of the stream: each record
appended is the stream's own next due record, or a record of the action,
as decided from the stream and from the action (its contents, its time,
its budget). Nothing else is read to decide a byte: not the wall clock
after the action's time is taken, not memory that a start does not
rebuild from the stream, not thread timing, not durability.

### 4.3. A draft wording for P2's extension

> **P2. A deterministic stream.** The bytes of the stream are a function
> of the accepted actions, their contents, times and order, and nothing
> else. An action is a call that writes: a transaction (`execute()` and
> the setters that commit), or `maintain()`. Everything the database writes
> by itself, its maintenance, is decided from the stream and the action
> that writes it, never from the clock, the timing, the threads, the cache
> or a restart. So a crash, a stop or a restart between any two records,
> inside an action too, leaves a prefix of the stream that the
> uninterrupted run would have written, and the next action continues it.
> A call that a crash or a stop interrupts is accepted if its record is in
> the stream; a `maintain()` call counts with the work it wrote.

What is outside it today (section 5): the Pub layer's index build and
cleanup threads, which commit on their own; the creating start's random
database id and its time; and, until Frans decides, the after-row charge
of 028-26 (section 6.5).

### 4.4. A crash inside an action

* **Between two records of a commit's maintenance**, on `main` the next
  commit does other work at other positions (028-54). With the design of
  section 6, the next action writes the rest of the maintenance due, the
  same records with the same bytes: the decisions read the stream only.
* **Inside a `maintain()` call**: on 031-04's prototype a part wrote up to
  six records (M1 to M6), and the budget was checked between parts, so a
  crash inside a part left a stream that no call writes. In the prototype
  of section 6 a part writes one record, so a crash between any two
  records leaves the stream of the same call with fewer parts.
* **Inside a record**: recovery drops or completes the torn record, as
  before (014-01), and the stream is the prefix before it.

### 4.5. What is promised today

* The README (its list of what BergDB is, "One stream"): "The same
  transactions in the same order give the same bytes." It says nothing of
  crashes or stops. On `main` a crash or a stop inside a commit's
  maintenance gives other bytes for the same accepted transactions
  (section 7.1, 031-04's prototype as `main`'s commits); whether the
  sentence promises it after a crash is 028-54's question for an RB entry
  (033).
* The Pub API's `Database` Javadoc speaks of what a crash keeps (the
  transactions, the stream's tail), not of the bytes. `Db.maintain(int)`'s
  Javadoc on 031-04's prototype says the cost is counted "so that the
  stream after the same calls is the same (010-01, P2)", between calls.


## 5. The inventory

Every code path that appends to the stream, with its inputs. Read at
`ff7b6534` (031-04's prototype with this item's text) on 2026-11-26, with
the help of a second agent for the paths outside reclaim. Only three
places append: `NodeStream.appendNodes` (from `Db.store` and
`Db.writePrimordialTransaction`), `RecoverableStream.writeMetaBlock`
(from its `append`), and recovery's fills in `RecoverableStream`.

### 5.1. Inputs not in the stream or the action, and how each is handled

* **N1. The trigger of a commit's maintenance**, an event in memory
  (`Reclaim.transactionCompleted` after the user record, in its call).
  * After a crash or a stop between the user record and its maintenance,
    the next commit runs its own maintenance from its own record: other
    work at other positions (028-54).
  * Prototype: `Reclaim.catchUp`. The maintenance due is read off the
    stream: whether the last record is a trigger (a user transaction's),
    its end and its time. Every action runs it before its own records.
* **N2. The clock at each internal record.** `DbClock.transactionBegin`
  reads the clock for reclaim's internal transactions too, so their times
  (and a done row's tEnd) follow the wall clock during the commit's call.
  * Prototype: `Trans.maintenance` and `DbClock.maintenanceBegin`. A
    record of maintenance takes the last record's time plus one, or a
    `maintain()` call's time if later. No clock is read.
* **N3. The time of a `maintain()` call, read again at every part**
  (031-04: `dbClock.currentTime()` per part), and so moved by the wall
  clock and by readers during the call.
  * Prototype: the call's time is taken once, at its first part
    (`DbClock.actionTime`), and serves every part's decisions (M5's and
    M6's `now`) and as the floor of its records' times.
* **N4. Times handed out to readers** (`currentTime()`). A record's time
  must be later than every time handed out (`DbClock`'s promise), and a
  time from the stream (N2) could be earlier.
  * Prototype: `DbClock.hold`. While maintenance is due, or a call that
    writes runs, `currentTime()` returns the last transaction's time
    instead of the clock. `Db.holdIfDue` sets it at the end of every call
    that writes and of a start.
* **N5. A part of a `maintain()` call wrote several records** (031-04's
  M1 to M6 in one part), with the budget checked only between parts.
  * Prototype: one record a part, the first that is due of M1 to M6.
* **N6. The step's after-row charge** (028-26): the bytes of the index
  nodes that a step's batch made dirty after its row was made, known in
  memory only, stored by a second record (`storeCurrent`). A crash or a
  stop between the two lost them.
  * Prototype: not charged, as before 028-26 (section 6.5; open question
    Q3).
* **N7. The done row's own record.** The last step stored the table with
  done, tEnd and pEnd in a record after its own; a crash between the two
  left the iteration not done, and the next step found its end at another
  time and position.
  * Prototype: the last step's row holds done, its time (tEnd) and its
    position (pEnd, the stream's length before the step's record).
* **N8. Interleaving of a commit and a `maintain()` call** (031-04's Q9
  handoff): where a commit comes between parts is thread timing.
  * Handled by the wording (section 4.1): the call counts as two.
* **N9. The Pub layer's index jobs.** `IndexBuilderImp`'s build thread
  and `IndexManager.startCleanup`'s cleanup thread commit on threads of
  their own, at minimum priority, with pauses of half a step's wall time,
  retry sleeps of 10 to 640 ms and the index manager's lock after three
  tries. The order of their commits among the user's is thread timing; the
  build's end key is read at the first step's moment; their progress is in
  memory, and a restart builds again from where the stream is.
  * Not handled. To make them so: run their steps inside actions, as
    reclaim's (a step at a commit, or a part of a `maintain()` call), with
    their progress in the stream. Open question Q4.
* **N10. The creating start**: the database id is random
  (`DatabaseId.createRandom`, SecureRandom, unless `DbBuilder.id()` or
  `testId()` gives one; the Pub layer never does) and goes into every meta
  block; the primordial record's time and the startup distance record's
  time are the clock's.
  * Not handled: the creation as action 0, with its id and time as its
    inputs, is the natural wording. Open question Q5.

### 5.2. Paths whose inputs are the stream and the action

* **A user transaction's record** (`Db.executeInner`, `Db.store`): its
  KVs, its time, and the take's share (`TransSeq.take`), which reads only
  what a start reruns (010-01, P2, 007-07).
* **The setters' records**: `setStartupDistance` commits a user
  transaction; `setRetainDuration` and `setReclaimInternalFraction` an
  internal one (`Reclaim.setSettings`), both from the argument and the
  call's time. In the prototype each writes the maintenance due first.
* **Meta blocks**: written only when a record reaches a multiple of
  200,000 bytes, from the stream (creation time, id, node size, the
  position of the record before).
* **Recovery's writes at a start** (`RecoverableStream.recover`,
  `fixLastTransactionIfNeeded`, `fixMetaBlockIfNeeded`): a torn record
  completed, a cut meta block completed, from the stream as found. Where
  the crash cut it is the crash itself. These run before a start's checks,
  so a start that is then refused may still append them.
* **No appends**: `stop()`, `close()`, `sync()`, `DbStarter`'s rerun, the
  eviction thread (tested by `EvictionInvariance`), the close thread,
  FileStream's cut thread, `Jmx`.
  * BufferedStream's thread is transport: the same bytes in the same
    order, whenever it writes.
  * Durability decides only when the physical cut removes the front
    (`Reclaim.cutIfDurable`): the cut's decision is written when it is
    made. The stream's bytes after the first available position do not
    depend on it.
* **Refusals** (`RerunException`, `DbException` before the go point) leave
  nothing. Whether a request is accepted may depend on timing (the STM's
  history); P2 is about the accepted ones.
* **`maintain()`'s dead hand** is charged by its time, but only after
  reclaim's last part of the call, and writes nothing.


## 6. The prototype

On the branch `031-05` of the clone c315, from c314's `031-04` at
`cfb195f3`; `java/` at `8a6bb105`. `prototype.diff` is its `java/`
against `cfb195f3`, so it shows this item's changes only.

### 6.1. Maintenance as a function of the stream

* **`Reclaim.catchUp()`** writes the maintenance due, a record at a time,
  each the first that is due of:
  * **B or S**, only while the stream's last record is a trigger: the
    begin of an iteration, or a step, decided as `main`'s
    `transactionCompleted` decided them, from the trigger's end
    (`lastEnd`) and time (`lastTime`);
  * **P**: the safe positions (`markSafePositions`);
  * **C**: the cut's decision, at the time of the stream's last record.
* **A trigger** is a record that is neither reclaim's own (031-03's R1) nor
  a setting of reclaim's: a user transaction's. `recordWritten` keeps
  `lastIsTrigger`, `lastEnd` and `lastTime` as records are written;
  `initFromDb` reads them off the stream's last record. So a start writes
  nothing and needs no recovery case.
* **Who calls it**: every action, under the write lock, before its own
  records (`Db.executeLocked` for a user transaction, `Db.maintain`'s
  parts, `setStartupDistance` before it sets the new value, and
  `Reclaim.setSettings`). A user transaction checks the database's state
  again after it, so a stop during it refuses the transaction.
* **Each record of B, S, P and C is reclaim's own**, so B or S comes at
  most once after a trigger, and P and C are each written once when due:
  the loop ends.

### 6.2. When: deferred (D1) or eager (D2)

* **D1, deferred**, the default (`Reclaim.eager` false): a commit writes
  its record only; its maintenance is written at the start of the next
  call that writes. This is the lead's proposal.
* **D2, eager** (`-Dproto315.eager=true`): a commit also runs `catchUp()`
  after its record, in its own call, as `main` does, and so do a
  `maintain()` call and the setters of reclaim's settings at their end
  (what the call's last part, or the new setting, left due: the safe
  positions, the cut's decision). So nothing is due between calls, and the
  next call's `catchUp()` finds nothing, unless a crash, a stop or a
  failure came between.
* **The bytes are the same.** The records are decided from the stream
  only, so which call writes them does not change them: with a write
  after the last action, D1 and D2 give the same stream (section 7.1).

### 6.3. The times

* A record of maintenance (`Trans.maintenance`: reclaim's tables, rows and
  steps) takes `DbClock.maintenanceBegin()`: the last record's time plus
  one, or the `maintain()` call's time if later. The clock is not read.
* A `maintain()` call takes its time once, at its first part
  (`DbClock.actionTime`), after the maintenance due.
* **The hold** (`DbClock.hold`): `currentTime()` returns the last
  transaction's time, not the clock, from the start of each call that
  writes until its end, and between calls while maintenance is due, so
  that every record's time is later than every time handed out.
  `maintenanceBegin` counts the records whose time had to follow a time
  handed out (`DbClock.holdFailures`): 0 in every run (section 7.4).

### 6.4. maintain(budget): one record a part

`Reclaim.maintainPart` writes at most one record, the first that is due
of 031-04's M1 (a pass's begin), M2 (a step), M3 (the safe positions), M4
(a take), M5 (the filler) and M6 (the cut's decision). Before each part,
`Db.maintain` runs `catchUp()`, as a commit may have come between two
parts. While an iteration runs, its steps come first: an older iteration's
take, filler and cut wait until it is done. A pass that a call begins
meets no other iteration that waits (031-04's M1), so this changes
nothing there.

For probes, `Db.maintain(int budget, int maxParts)` ends after at most
`maxParts` parts that wrote: the call with a smaller budget.

### 6.5. The step: done in its own row, no after-row record

* **The last step's row holds done**, its time (tEnd) and its position
  (pEnd, the stream's length before the step's record, which no record
  start lies between), set by the row's value transformation. `main`'s
  separate table record after it (N7) is gone; `initFromDb` takes a done
  current row into the table.
* **The after-row record of 028-26 is dropped** (N6): its charge is known
  in memory only. The step's row charges what its touch made dirty, as
  before 028-26. The unit tests show the size of what is no longer
  charged: in `testAllowanceCountsIndexNodes`, the done row's `rewritten`
  is 419,353 where 028-26 charged 446,665 (6 % less); in
  `testAllowanceCountsNodesMadeAfterTheRow` at node size 8, 9,488 where
  it charged 12,848 (26 % less). 028-26 reported 24 % to 30 % at node
  sizes 30 and 8. Reclaim then writes up to that much more than its
  internal fraction. Open question Q3.

### 6.6. Tests changed

`BEFORE COMMIT OK` needed:

* `ReclaimMaintainTester.testCommitGoesBeforeTheNextPart` is unchanged:
  it failed while `Db.maintain` counted its calls under the write lock,
  which the test holds; the prototype counts them without it.
* Five tests of `Reclaim.Tester` check what a commit's own call writes
  after its record, and run eagerly (D2) through `eagerly()`:
  `testUserTransactionLeavesTimesForReclaim`,
  `testStepScansAtItsOwnTime`, `testEndKeyBoundsTheScan`,
  `testSafePosAfterTheCallsRecords` and `testCrashBeforeIterationEnd`. The
  last now crashes after the last step, as no table record follows it.
* `testAllowanceCountsIndexNodes` and
  `testAllowanceCountsNodesMadeAfterTheRow` expect the charge without the
  after-row bytes (section 6.5).

### 6.7. Counts

Lines of code (comments and blank lines excluded, `git diff -w` against
`cfb195f3`):

* production: 231 added, 42 removed (`Reclaim` 117 and 39, `Db` 79 and 3,
  `DbClock` 34, `Trans` 1);
* tests: about 32 added and 8 removed, in `Reclaim.Tester`.
* By part, about: `catchUp` and its trigger 60; the checks without writing
  for the hold (`catchUpDue`, `safeDue`, `cutDue`, the split of
  `pretruncateIfPossible`) 35; the hold and the times 60; one record a
  part 25; the D1/D2 switch and the probe's `maintain(int, int)` 30; the
  done row in the step, less the after-row record and the table, 10 net.
* **New state**: none in the stream; in memory, three fields read off the
  last record (`lastIsTrigger`, `lastEnd`, `lastTime`), the hold and the
  call's time. **Recovery cases**: none. **Format**: no change of a
  record's format; a done row is stored in the current row first; the
  after-row record and the done table record are no longer written.


## 7. Evidence

### 7.1. Crashes and stops at every record boundary

`P2CrashProbe SEED ACTIONS SD`: a seeded workload of actions, each with
its time (puts of 0 to MAXV bytes at KEYS keys, some of up to 8 keys,
deletes, empty transactions, a few setters of the startup distance and of
the retain duration, and `maintain(B)` calls, ending with an empty
transaction). For every record k of the uninterrupted run, a run of the
same actions is crashed after record k (its test hook throws, so the
database fails and appends nothing more, P7) or stopped there (the hook
calls `stop()`); then a start from the stream, and the actions after it
by section 4.1's rule. The continued stream is compared with the
reference, byte for byte, with its length and its decided cut. The
reference is the uninterrupted run, or, after a crash inside a call that
wrote m parts, the uninterrupted run with that call ending after m parts.

Run on 2026-11-26 (`p2crash-runs.txt` lists the configurations and their
summary lines):

* **The prototype: every boundary gives the same stream.**
  * D1: 17 runs of 16 configurations, every record (every 5th in one of
    2,003 actions, every 9th in one of 1,003 actions with values of up to
    80 kB at node size 8): 8,473 crashes and 8,473 stops with the same
    stream, 0 different.
  * D2, on the prototype as committed (after its change of 14:00, which
    makes a call write what it leaves due): 13 configurations (every 3rd
    record in one of 1,503 actions with calls of 100,000 units): 7,152
    crashes and 7,152 stops with the same stream, 0 different. Before
    that change, 6,843 and 6,843, also 0 different.
  * Startup distances of 200 bytes to 50 kB; budgets of 100 to 100,000;
    node sizes 8, 30 and the default; 200 to 3,000 keys; calls of
    `maintain()` in 3 % to 50 % of the actions. About 4,000 of each
    kind are inside `maintain()` calls, each compared with the call ending
    after that many parts.
  * Every crashed or stopped stream ended exactly at the record's end:
    a stop writes nothing after the record it comes at.
* **D1 and D2 give the same stream**: the same digest in each of the 12
  configurations run in both on the committed prototype.
* **031-04's prototype** (`cfb195f3`, whose commits maintain as `main`
  does), the same probe at the boundaries outside calls (it has no
  `maintain(int, int)`): 195 of 1,857 differ, crash and stop alike (seeds
  3, 11, 12 and 14: 44 of 418, 40 of 411, 49 of 415, 62 of 613). The
  first differ at a user record whose maintenance follows it, and at
  boundaries between its maintenance records.

### 7.2. MidCallProbe (031-01)

031-01's `MidCallProbe` (a crash right after a user record whose
maintenance begins an iteration, before the begin) gives the same bytes on
the prototype: "lengths 149088 149088, same bytes true". On `main` and on
031-01's and 031-04's prototypes it gave other bytes from that record on.

### 7.3. StreamDigest and RestartInvariance

Run on the prototype's jar (D1, and D2 with `-Dproto315.eager=true`):

* **StreamDigest quick** (11 configurations, 4 modes each: plain, reads,
  restarts, restarts once): in D1 and in D2 (D2 run again on the committed
  prototype), "the modes give the same stream" in every configuration.
  * D1 against D2: 40 of 44 digests the same. The 4 others are the four
    modes of l3-node62, where D2's stream is 11,456 bytes longer: the
    maintenance after the workload's last transaction, which D1 leaves to
    a next call (section 6.2).
  * Against `main` or 031-04 the digests differ, as they must: the times
    of reclaim's records, the done row in the step, no after-row record
    and one record a part change the bytes.
* **RestartInvariance with reclaim**, level3.sh's four configurations of
  step 3 at its full size (2,000 transactions; every1 1,000, with a
  restart after every transaction), in D1 and in D2 (D2 twice, before
  and after the change of 14:00): "STREAM: identical", the same cut, and
  the six checks with 0 failures, in all twelve runs; level1.sh's
  configuration of step 5 (no reclaim) the same in D1.

### 7.4. The hold

`HoldProbe SECONDS READERS`, with the system clock: a writer commits puts
and calls `maintain(100)` every 20th action, while readers call
`currentTime()` and read at it; R = 1 s, sd 2,000 bytes.

* 20 s, 3 readers, the writer without pauses: D1 1,210,609 actions, D2
  1,034,283; 0 hold failures in both.
* 10 s, 2 readers, a pause of 1 ms after each action: D1 7,621 actions,
  2.9 % of 49.6 million `currentTime()` calls at the last transaction's
  time; D2 6,571 actions, 3.0 % of 45.1 million, and on the committed
  prototype 7,440 actions, 2.4 % of 52.4 million; 0 hold failures in all.
* So every record of maintenance had a time later than every time handed
  out. With the writer idle a millisecond between actions, the clock was
  held for about 3 % of the reads in both designs here.

### 7.5. 031-04's cases

Run on the prototype (D1), with 031-04's figures in brackets:

* `HoleProbe 4000 20000`: kept 71,368 bytes (116,880), the twin 52,664
  (53,120); `HoleProbe 20000 20000`: 125,984 (117,872), the twin 113,512
  (116,672). The last call that wrote: 1,605 of 10,000 in both (1,605).
* `IdleLiveProbe LIVE SD 20 10`, nothing written in the last 10 R in
  every case:
  * 30,000 values at sd 1 MB: kept 5,947 kB (6,070);
  * 15,000 at 1 MB: 2,976 kB (3,056);
  * 100,000 at 1 MB: 19,793 kB (20,237);
  * 100,000 at 5 MB: 19,604 kB (20,101).
  * The last call that wrote: 2,039 to 2,339 (2,042 to 2,337).

### 7.6. Gates

* **`java/before-commit.sh`**: `BEFORE COMMIT OK (112 s)` on `2173b13a`
  at a load of about 16 (week.sh ran), and `BEFORE COMMIT OK (68 s)` on
  `8a6bb105`, the prototype as committed, at a load of 6 to 11. The tests
  changed are those of section 6.6.
* **`count-gates.sh all`** (D1): `COUNT GATES OK`.
  * G1 104,560 bytes (031-04: 105,200), G2 1.230 (1.227), G3 4.318
    (4.721).
  * G4's M5, dead key klongs over the twin's: 1.933 (29 of 15), where
    031-04 had 1.429; the limit is 2.0. The same in D2 (`g4` alone with
    `-Dproto315.eager=true`), so it comes from the prototype's other
    changes, not from D1; not examined.
  * G5: the stream kept, at its most in the last R, 179,456 bytes
    (031-04: 102,184), the twin's 199,296; the last call that wrote is
    2,003 of 20,000 (031-04: 2,002). Not examined.
* **The conformance's reclaim and crash sets**, run with the unchanged
  trace checker (built in c314 from the same lean/, through `CHECK`):
  * D2 on the committed prototype: `CONFORMANCE OK` in both. The reclaim
    set, 40 traces: C-CUT 0 of 884 CUT lines fail, C-STEP 0 of 25,888
    transactions, C-R 0 failed probes. The crash set, 15 traces: 0 of 280
    CUT lines, 0 of 6,558 transactions, 0 failed probes.
  * D2 before the change of 14:00: C-CUT and C-STEP 0 fail, but r-maint's
    and c-maint's traces had exporter errors: after a `maintain()` call
    that ended with the safe positions or a cut's decision due, the next
    commit wrote them before its own record, which `TraceExport` does not
    take (section 8). The change made the call write them.
  * D1: stopped after 15 traces of the reclaim set, each with the same
    exporter errors, as a commit's maintenance comes first in the next
    call (section 8).


## 8. What it costs

* **The work is the same.** The same records are written in both designs,
  only in another call (D1) or in the same (D2). In D1 a commit's call
  writes the previous commit's maintenance before its own record, so what
  a commit waits for (P1) is its predecessor's maintenance where `main`
  makes it wait for its own: the same bound.
* **D1: the last action's maintenance waits for the next call.** After the
  application's last commit, its step, its safe positions and its cut's
  decision are not written until the next write. A cut that `main`
  decides in the last commit's call stays undecided, and the stream before
  it kept, until then. `maintain()` writes it first, so an application
  that calls `maintain()` does not see this.
* **D1: the clock is held between calls while maintenance is due.**
  `currentTime()` returns the last transaction's time until the next
  write; an application that writes once and reads for an hour sees no
  time move. Relative times (`Time.resolve(tz, now, "-10 s")`) then
  resolve against a stale now. In D2 the clock is held only during calls
  and after a crash or a stop until the next write.
* **D1: read-modify-writes refused.** Reclaim's copies at the next call
  come after a read time taken while they were due, so a transaction that
  read a copied key is refused once (`RerunException`) and done again.
  `RwProbe N KEYS VALUE SD`, 20,000 read-modify-writes of a key read at
  `currentTime()`, R = 1 s:
  * 200 keys of 1,000 bytes, sd 2,000: D1 refused 45; D2 0; 031-04 0;
  * 10,000 keys of 1,000 bytes, sd 100,000: D1 2; D2 0; 031-04 0;
  * 100,000 keys of 100 bytes, sd 1 MB: 0 in all three.
* **D1: the tools.** `TraceExport` takes a call's first record for its
  user record ("not the first of its call" otherwise). In D1 the
  maintenance due comes first: each of the 15 traces of the conformance's
  reclaim set checked in D1 had such errors (20 in r-small-1), and its
  restart probes (C-R) compared other records. D1 would need the trace
  to mark the calls (section 9's CALL lines). D2 keeps the user record
  first, as every call writes what it leaves due, and the conformance's
  sets pass (section 7.6).
* **Both: the after-row charge** (section 6.5): reclaim may write up to
  about a quarter more than its internal fraction at small node sizes,
  until Q3 is decided.
* **Both: one record a part.** More parts per call; a call's cost is
  still the bytes written and a quarter of the bytes read. 031-04's
  figures of section 7.5 are about the same; G5's stream kept is higher
  (section 7.6).
* **The take**: D1 and D2 write the same records, so the same shares. In
  D1 the take that a commit's maintenance writes comes in the next call.
* **Code**: 189 more lines of production code than 031-04's prototype
  (section 6.7); the hold and the D1/D2 switch are about 65 of them.


## 9. A sketch of the Lean statement

By a second agent of lead-1126 (2026-11-26), from lean/README.md, 030's
readme, 030-26 and the model; nothing built.

* **What is proved today.** The writer is a function: `step`
  (lean/SIS/Algorithm.lean, 184) appends one record a transaction, and
  `run` (222) folds it over a given list. `T1_crash` (Theorems.lean, 45):
  a crash leaves a prefix of whole records. `T2_restart` (Theorems.lean,
  60) and `T12_restartCut` (ReclaimTheorems.lean, 167): restarts, with
  cuts, change no record. For PE's histories, `full_restart` and
  `full_cut` (contract/Contract/BridgeFull.lean, 89 and 120). All for a
  list given in advance: which internal transactions come is not chosen
  in Lean.
* **The statement.** A new file, lean/SIS/Due.lean: an action is an
  execute of a transaction or a maintain with a budget, each with a time;
  a policy `due : Ctx → Option T` reads the stream, the latest view and
  the dirty set D, all of which a start restores; `act` appends what
  `due` gives, then the action's records; `runAct` folds `act`.
  `runCrash` runs a schedule with a crash after any record, a restart, and
  the actions after it. The theorem:

  ```lean
  theorem T16_crash (hok : RunOK sp al (txsOf (accepted cs))) (hst : AlgOK sp al)
      (hm : DueMono po) (he : DueEnds po K) (hp : MaintPrefix po) (ht : TimesMono cs) :
      (runCrash cs).S = (runAct (accepted cs)).S
  ```

  with `accepted` dropping an execute crashed before its record and
  counting a crashed maintain with a smaller budget.
* **Its assumptions**: AlgOK (the existing `algOK_of`,
  Proof/StepInv.lean, 59); DueMono (what is due is the same later and
  inside a call); DueEnds (the loop of due records stops); MaintPrefix (m
  records of maintain(b) are those of a maintain(b') with b' ≤ b, the
  reason for one record a part); TimesMono; with cuts, `PolicyCutOK` for
  `due`.
* **What is easy and what is the work.** "The state after a restart is
  the running database's at that prefix" is there: `T1_strong`
  (Proof/Recovery.lean, 91), `Rel` and `step_congr` (Proof/Restart.lean),
  `T2_strong`. The work is a lemma about lists by induction over the crash
  schedule: the loop resumed inside itself gives the rest of the loop,
  and due records written by a call that is then dropped are those that
  the next call would write.
* **What would change in lean/**: additions only, no Mathlib, about 800
  to 1,600 lines (Due.lean, DueTheorems.lean, Proof/Due*.lean, an example
  with `#guard`), and `T16_crash` in lean/README.md's list of axioms
  printed. No existing statement changes; lean/contract, the checkers
  and `tracecheck` are unchanged. Optional: a corollary for PE.
* **What stays tested**: that Java's maintenance is the model's `due`,
  its inputs read from the stream only (this item's probes; later a C-DUE
  check in `tracecheck`, with CALL lines in the trace format 027-02); the
  clock (TimesMono).
* **030's map** would gain a direction, "P2 with crashes (031-05)": the
  statement once Frans approves the wording; C-DUE after the design lands;
  optionally a concrete reclaim `due` in Lean whose steps meet `StepsOK`.
  030-26 would change with it (crashes inside calls; that the internal
  transactions are given today, not chosen).


## 10. Open questions for Frans

* **Q1. The wording** (section 4.3).
  * Options: (a) the draft, which names the setters and counts an
    interrupted call by what it wrote; (b) the draft without the setters,
    which then become `execute()` calls in the API; (c) a narrower goal,
    commits only, `maintain()` left as today.
  * Recommended: **(a)**.
* **Q2. When the maintenance is written.**
  * Options:
    * (a) D1, deferred to the next call (the lead's proposal);
    * (b) D2, in the call that made it due (a commit, a `maintain()` call,
      a setter), and by the next call after a crash, a stop or a failure;
    * (c) as (b), and a start that writes the maintenance due after a
      crash or a stop as its last act (as 031-01's start wrote w): the
      clock is then never held between calls, and a call's first record
      is always its own; but a start writes, also one that only reads,
      and that is a recovery case.
  * The bytes are the same in all three (section 7.1). D1 costs a held
    clock between calls, refused read-modify-writes, a last cut that
    waits, and the tools' notion of a call (section 8). D2 costs none of
    these but after a crash or a stop.
  * Recommended: **(b), D2**.
* **Q3. The after-row charge of 028-26** (N6, section 6.5).
  * Options:
    * (a) not charged, as in the prototype: reclaim may write up to about
      a quarter more than its fraction at small node sizes;
    * (b) a deterministic charge known before the batch: an estimate of
      the nodes that PE's batch makes (a top node, and the replacements
      and splits that the step's puts can cause), stored in the step's
      row;
    * (c) charge the bytes of reclaim's records as written (their record
      lengths, read off the stream at the next step) in place of the
      bytes made dirty: a change of the cost model;
    * (d) keep 028-26's second record, and a start that recomputes the
      charge by running the step's batch again on the state before it:
      the start does not have that state.
  * Recommended: **(a) for 2026.7 if the direction lands, and (b) as a 028
    entry**, measured with `count-gates.sh` G1 to G4.
* **Q4. The Pub layer's index jobs** (N9).
  * Options: (a) outside the goal for now, named in the wording; (b) their
    steps inside actions (a step at a commit or a `maintain()` part, as
    reclaim's), their progress in the stream: a design item.
  * Recommended: **(a) now, (b) as an item** after this one.
* **Q5. The creating start** (N10).
  * Options: (a) the creation as action 0, its id and time its inputs;
    (b) the id derived from the application's input only (no random id).
  * Recommended: **(a)**.
* **Q6. The hold of `currentTime()`** (N4).
  * Options: (a) hold the clock while maintenance is due, as built; (b) no
    hold: records of maintenance may have times before a time handed out
    to a reader. A read of a user key at such a time still returns the
    same value (a step copies values), but reclaim's own keys and the
    values' positions change at a time already read, against `DbClock`'s
    promise.
  * Recommended: **(a)**, with D2 (Q2), where it is short and rare.
* **Q7. One record a part** in `maintain()` (N5): needed for a crash
  inside a call to leave the stream of a call. Recommended: **yes**.
* **Q8. A refused call after a crash or a stop** writes the maintenance
  due before it is refused (D2), or always (D1). The stream is then
  longer than that of the accepted actions, by maintenance that the next
  accepted call would write: a prefix of the uninterrupted run (section
  4.2, point 2). Recommended: **accept**. The alternative, the maintenance
  after every check that may refuse the call, makes those checks (the STM,
  the transformations) read a state that the maintenance then changes.
* **Q9. The Lean statement** (section 9). Recommended: **after the design
  lands**, as a direction in 030; C-DUE later.


## 11. State

2026-11-26, by an agent of lead-1126.

* **Done:**
  * the invariant and a draft wording (section 4);
  * the inventory (section 5);
  * the prototype, on the branch `031-05` of the clone c315 (`java/` at
    `8a6bb105`, with `BEFORE COMMIT OK`), `prototype.diff` against
    031-04's `cfb195f3` (section 6);
  * the evidence (section 7) and the costs (section 8);
  * the Lean sketch (section 9) and the open questions (section 10).
* **Not done:**
  * night.sh, level3.sh and level4.sh in full, `timing.sh`, the apps of
    `apps.sh`, the 10M-key runs of 031-04;
  * 028-54's RB question (section 4.5 has the README's sentence);
  * the Pub layer's index jobs (N9) and the creating start (N10): named,
    not changed;
  * G4's M5 (1.933) and G5's stream kept (179,456 bytes), higher than
    031-04's (section 7.6): not examined;
  * no independent review.
* **Next:** Frans's decisions on Q1 to Q9; then, if the direction is
  taken, a review by Codex of the prototype in D2, and a design item for
  the landing with 031-04's.


## Log

2026-11-26. Created by lead-1126 from Frans's decision of the same day:
the goal, and a study of it on 031-04's prototype.

2026-11-26. The study, by an agent of lead-1126 in the clone c315 (branch
`031-05`): the invariant and a draft wording of P2's extension; the
inventory, with ten inputs outside the stream and the actions; a
prototype in which a commit's maintenance is decided from the stream only
and written in the next call (D1) or its own (D2), the same bytes either
way; 15,625 crashes and 15,625 stops at record boundaries, inside
commits and `maintain()` calls, each continued to the uninterrupted run's
stream (031-04's prototype: 195 of 1,857 differ); the conformance's
reclaim and crash sets OK in D2; the costs of D1; a Lean sketch; nine
questions for Frans. Sections 4 to 11, `prototype.diff`,
`probes/`, `p2crash-runs.txt`.
