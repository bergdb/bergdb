# 031-06. One record an action

Created 2026-11-27 by Frans Lundberg. Status: open.

A prototype of option (e) of A1 (006-37, section 4.1): every accepted
action appends exactly one record, and a commit's record holds the
maintenance that reclaim owes, decided from the stream before the record.
Built on 031-05's prototype (branch `031-05`, `4135ba2a`), which is on
031-04's (`cfb195f3`). The study of (e) that it builds, by an agent of
lead-1127 (2026-11-27, 09:44 to 11:15), is `study.md`; Codex's
independent review of the studies of (c), (d) and (e) (2026-11-27, 10:55)
is `codex-studies.md`, and its findings E1 to E6 and its three tests
are cited by their names. The prototype's code is `prototype.diff`
(java/ against `4135ba2a`), its probes and their scripts are in
`probes/`, and the summary output of the runs of section 4 in `runs/`.

A1 was decided as (e) on 2026-11-27 (section 8), after the independent
review of the prototype, `review-fable.md` (its probes in
`review-probes/`); the landing on `main` is section 9. Also here:
`study-d.md`, the study of option (d), the compound unit, not taken, and
`p2-draft.md`, a draft of P2's extended wording, a proposal (010 is
unchanged).


## 1. The decision

Frans, 2026-11-27 (006-37, section 2):

* 09:38: A1 is the day's focus. Backwards compatibility of the stream
  does not count against a design; stability, simplicity and provability
  going forward do.
* 11:16: a part of `maintain(budget)` takes its own time from the clock,
  as a transaction does, and the part is the unit: an action is a
  transaction, a setter or a part, each with its time.
* 11:18: a prototype of (e) is built today, as 031-06. A1 stays open
  until its evidence; (c) is the fallback. Fixed for the prototype:
  reclaim's plan and apply behind an interface with an empty second
  implementation; the part as the unit; the setters carry no maintenance;
  the step has an allowance of its own in the record, so that large
  transactions cannot starve reclaim (Codex's E5); a key of reclaim's is
  the witness of reclaim's own record (Codex's E2); the copy mark on a
  value node (Codex's E1); the after-row charge of 028-26 stays dropped
  and is measured; Lean, the trace format and the contract checkers are
  out of scope.


## 2. The design as built

On the branch `031-06` of a clone of c315 (outside the repository),
from `4135ba2a`. Each rule says what, when, by whom, and how it is
checked; the evidence is in section 4.

1. **One action, one record.**
   * What: an accepted commit (`Db.execute`) appends exactly one record;
     a setter one if it changes its setting, none if the setting is in
     force; a part of `maintain()` one; nothing else appends but
     recovery's completion of a torn record. A part with nothing due
     writes nothing and gives its time back.
   * By whom: `Db.executeLocked`, under the write lock, for all three:
     `maintainPart()` runs an empty internal transaction marked
     `Trans.part` through it.
   * Checked: `P2CrashProbe` counts the records of each action in every
     reference run (23 runs: records = accepted actions in each), and
     `testMaintenanceNone`, `testUserTransactionLeavesTimesForReclaim`
     (one record).
2. **The boundary.**
   * What: `Maintenance` (a new interface, `Maintenance.java`) with two
     calls. `plan(t, kvs)`: what the record of action `t` carries, from
     the stream before it, the record's time and the action's KVs as
     they will be put; it reads only and changes no memory of reclaim's
     (it works on copies of the rows). `apply(plan, t)`: after the
     record is appended, reclaim's memory as the plan made it, then the
     pending physical cut once the stream is durable past it. All policy
     (when an iteration begins, a step's size, when to cut) is in
     `Reclaim.plan`. `Maintenance.NONE` is the empty implementation
     (`DbBuilder.maintenanceNone()`).
   * When: `plan` after the last check that may refuse the action
     (`transformValues`), before the go point; `apply` after `store()`.
   * By whom: `Db.planMaintenance` and `Db.executeLocked`; `Reclaim`
     implements it. Db reaches the records' maintenance only through it.
     Outside it stay the settings (`setSettings`), the start
     (`initFromDb`), the statistics (`recordWritten`), and the physical
     cut after `maintain()`'s sync outside the lock
     (`pendingCutDurableAt`, `cutIfDurableNow`), which writes nothing.
   * Checked: `Reclaim.Tester.testMaintenanceNone` (a Core test with
     NONE: 2,000 actions, no copy and no key of reclaim's in any record,
     `maintain()` writes nothing, nothing cut, every value there).
3. **A commit's record holds its maintenance, decided from the stream
   before it** (`Reclaim.planCommit`).
   * What: B (the begin of an iteration) or S (a step), then P (the safe
     positions), then C (the cut's decision), each as `main` decided it
     after a commit, with L0, the stream's length before the record, for
     the growth, pStart, pEnd and pSafe; the time of the stream's last
     record (`lookupTime(MAX)`, the state at L0) for tStart and for the
     end key (`lastKeyAt`); the record's own time for tEnd and the cut's
     now; the startup pos and the last valid meta block as the last
     record left them. No decision depends on another in the same record
     (study, section 1, "Order"). A decision that needs the record's own
     length or take is made in the next record.
   * Checked: the probes of section 4.1 (the bytes at every boundary),
     StreamDigest and RestartInvariance (4.4).
4. **The plan's KVs** (`Reclaim.planStep`, `finishPlan`).
   * What: the step's copies, each live value stored before pCut that
     the scan met at the state before the record, with its value; the
     row (`-current.txt`), and the table (`-table.txt`) if B, P or C
     changed it or a part's M4 or M5 writes it, both by value
     transformations that run in `Db.putKvs` after the touch
     (`Kv.planned`; they read no previous value). A copy at the row's or
     the table's key is replaced by it. The touch walks the paths of the
     copies and the row (`Plan.touchKeys`). Db merges the plan's KVs with
     the action's in key order, one KV a key (`Db.merge`; a Bug if a key
     were in both, which fails the database).
   * The copies are neither reads nor writes of the STM: the scan reads
     the state before the record, under the write lock, after the
     transaction's conflict check; no copy enters `writeKeyHashes`.
   * Checked: `testCopyAtAKeyTheActionWrites`, `SafetyProbe` (4.3).
5. **The step's room on top of the transaction's** (006-37, section 2,
   11:18; Codex's E5). What, derived and assumed: section 3.
   * What: the user's limits and checks are unchanged (L1 to L5, 005-17's
     7/8 and 005-31's 15/16 of `StoredTrans.recordLimit`). A record that
     carries maintenance may take `StoredTrans.recordCap()` =
     min(`MAX_RECORD_SIZE`, `recordLimit` + `stepRoom()`), with
     `stepRoom()` = one value node of the largest size a transaction can
     store (`maxValueNode()`: L4 at an L3 key, at most `valueLimit()`) +
     256 kB (`STEP_FIXED_ROOM`: the scan's other KVs, 16 kB, the row and
     the table) + `recordLimit` / 16 (the step's index nodes). The take
     and the serializer use the cap (`Trans.recordCap`). The step's
     scan keeps 015-50's rule (its first KV always, later ones within
     `valueLimit()`) and its 16 kB (`MAX_STEP_SIZE`, 011-04). So no step
     waits for the room a transaction leaves, and an old value of the
     largest size is copied.
   * Checked: `SafetyProbe` at record limits of 100 kB to 1 MB, with
     transactions whose values take 0.5 to 0.8 of the value limit in 6 %
     of the actions (4.3); `LimitsTester` and `DbTester`'s lowered-limit
     tests in `before-commit.sh`.
6. **Reclaim's own record and a** (Codex's E2).
   * What: a is the position of the last record of the application's
     (031-04, R3). `apply` sets it to the record's position for every
     record but a part's. Every row that a record stores holds a as it is
     after that record: its own position, L0, for a commit's, a as
     before for a part's. A start (`initFromDb`) takes a record as
     reclaim's own only if it holds a key of reclaim's that is not a copy
     (a witness), and then reads a from the rows, else the record's
     position. An empty commit has no witness and tells by its position,
     as the running database set it.
   * Checked: `P2CrashProbe` compares the start's memory (a, the first
     available position and time, the settings, every row) with the
     running database's after every record, at every boundary: 27,720
     starts, all equal (4.1); `FaultProbe` after each fault (4.2).
7. **The copy mark** (Codex's E1).
   * What: byte 6 of a value node, 1 for a copy (`StoredValueNode`;
     until now zero, skipped); byte 7 stays zero; any other value is
     refused at the parse (`StreamFormatException`). Under the checksum
     (bytes 0 to 7 are in it). Set by the serializer from
     `TransNodes.copyKeys`, which Db sets from the plan before the
     append; parsed into `StoredValueNode.isCopy()`, which `getTrans`
     gives. `ConnectionImp.transactionInfo()` follows a value back only
     if its node is a copy, and lists the record's KVs without the
     copies. A copy at a key that the action writes, by its key as
     transformed, is dropped (Codex's E4), and the step's progress
     (lastKey, kvCount, rewritten) moves only in `apply`.
   * Checked: `StoredValueNode.testCopyMark`, `PubTester`'s
     `transactionInfo` tests, `PubInfoProbe` (12,034 calls through copies
     in commits' and parts' records, with cuts and restarts) and
     `SafetyProbe`'s walks (1,488,553, through 1,978,277 copies).
8. **Refusal, failure and stop** (study, rule 5; Codex's E6).
   * What: a commit is refused only by its own checks, before the plan.
     A stop during the plan, or before it returns, refuses the action
     with nothing written: `planMaintenance` gives the transaction back
     (`giveBack`: its keys, values and time) and throws the
     `DbStoppingException`; the admission check after the plan does the
     same when the plan read nothing. Any other exception from the plan
     on fails the database (P7). After the go point a stop does not
     refuse: the close waits for the record.
   * Checked: `FaultProbe` (4.2).
9. **Times.** Every record's time comes from `DbClock.transactionBegin`,
   a part's too (as a user transaction's: refused after `LAST_USER_TIME`).
   There is no hold of `currentTime()` and no maintenance time: 031-05's
   `DbClock` changes are gone. The 1,024 kept times and top node ordinals
   (015-55, 005-02) stay (question Q4).
10. **`maintain(budget)`.** Each part is an action with its own time and
    one record, the first that is due of M1 to M6 (031-05, section 6.4),
    built through the same path as a commit (`Reclaim.planPart`). A call
    does the parts that fit its budget; 031-04's deterministic cost
    (bytes written and a quarter of the bytes read) stays.
    `maintain(int, int)` stays for probes. Checked: `P2CrashProbe`
    inside calls, the count gates (4.5).
11. **The setters carry no maintenance** (`Trans.noMaintenance` for
    `setStartupDistance`; reclaim's settings are an internal record).
    What a setting makes due is decided by the next record that carries
    maintenance. Checked: `ReclaimRetentionTester` (031-05's F1:
    `testRestartWithOtherRetention` passes unchanged).
12. **The after-row charge (028-26) is not made.** The row charges the
    copies' bytes and what its touch made dirty. Measured in 4.6.

**Removed from 031-05's prototype:** `catchUp`, `catchUpRecord`,
`commitWork`, the trigger (`isTrigger`, `lastIsTrigger`, `lastEnd`,
`lastTime`), the "would write" predicates (`catchUpDue`, `safeDue`,
`cutDue`), the hold and the maintenance times (`DbClock.hold`,
`holdFailures`, `maintenanceFloor`, `actionTime`, `maintenanceBegin`,
`Trans.maintenance`, `Db.holdIfDue`, `maintainCalls`), the D1/D2 switch
(`Reclaim.eager`, the tests' `eagerly`), `inPart`. From `main`'s and
031-04's: `Reclaim.transactionCompleted` and `Db.TransactionListener`,
the listener call after a commit and its `DbStoppingException` catch
(015-53), reclaim's `db.execute` of steps, rows and tables (`step`'s,
`storeCurrent`, `storeTable`, `markSafePositions`,
`pretruncateIfPossible`). Reclaim's only `db.execute` left is the
settings record of a setter.

**Not built** (out of scope): Lean; the trace format (027-02) and
`TraceExport`'s notion of records (it compiles); the contract checkers;
the C clone; the Pub layer's index jobs; a warm-up of the step's scan
before the lock. That warm-up would go in `Db.executeInner`, beside the
transaction's own `warmup(t)` before the write lock: the scan of the next
step's range at the latest time, so that the scan under the lock meets
its nodes in the cache.


### 2.1. Where the code departs from the study

The study (`study.md`) is a proposal; where the code contradicted it, or
a decision of Frans's or a review changed it, the prototype follows the
code and the decision:

* **The room** (study, section 2 and rule 4): the study sized the step
  to the room the transaction leaves and skipped it when none was left.
  Codex's E5 showed that a run of such transactions can keep reclaim from
  moving; Frans fixed an allowance of the step's own (11:18). Built as
  rule 5, with section 3's derivation.
* **Reclaim's own record** (study, section 4, rule 10): "every KV a copy
  or a key of reclaim's" holds for an empty commit, which has no row that
  holds a (Codex's E2). Built as rule 6: a key of reclaim's that is not a
  copy is the witness, and a commit's rows hold its own position as a.
* **A part's time** (study, E4 of its section 11): Frans chose the part's
  own time (11:16); no hold inside calls either.
* **The kept times and top node ordinals** (study, rule 7, "may go"):
  kept; question Q4.
* **P1** (study, section 6, "confirmed, as an inference"): measured
  instead (section 4.7). The commit that carries a step took less than
  031-05's commit and its step's record; readers see the commit later by
  the scan's time, which the study had named.
* **A stop during the plan's reads**, which the study's section 5 did not
  name: the scan's reads are refused while the database stops
  (`getMany`'s state check). Built as a refusal with the transaction given
  back (rule 8; Codex's E6).
* **The plan's value transformations**: `Db.putKvs` read the previous
  value for an internal transaction's transformation, a read after the go
  point that a stop would refuse; the row's and the table's read none.
* **The table's KV** is made by a value transformation after the touch
  whenever the record stores it, not only when it comes with a step
  (study, rule 3): one path.
* **A Trans executed again** (its Javadoc allows it): the plan's fields
  of a record (the touch, the dirtied counts, the take's target, the cap)
  would have stayed on a user's Trans; they are set at every execution
  and cleared after the record. Not in the study.
* **Tests**: the study expected 150 to 300 lines of tests changed; five
  tests changed and three added (section 4.0), the conformance's traces
  not touched.
* **The after-row charge**: the study cited 6 % and 26 % from two unit
  tests; passes of small values leave 25 % (node size 30) and 39 % (node
  size 8) of the charge uncharged (section 4.6).

## 3. The record limit and 024-17's bound for a mixed record

* **Derived, at the release's limits** (024-17, sections 5.2a, 5.3 and
  5.5, the same arithmetic). A transaction within L1 to L5 has own bytes
  of at most 33.6 MB and a dirty set, by the count with q, of at most
  1.47 GB at node size 8 (0.90, 0.91 and 1.33 GB at 14, 30 and 62). The
  step's KVs are a transaction of at most about 459 operations (024-17,
  5.5); its segments are at most 16,000 / 8 by the scan's count, and
  those of one more KV, at most 60 (assumed below), so 2,060. By the
  count with q, c (H + 2) nodes a segment and 14 an operation (c = 14,
  H = 61 at node size 8; 9 and 38 at 14; 8 and 21 at 30; 8 and 16 at
  62), its dirty set is at most 1.82 M nodes, 350 MB at node size 8 (215,
  210 and 320 MB at 14, 30 and 62). The count is a sum over operations,
  so the record's transaction, the action's and the step's together, has
  a dirty set of at most 1.82 GB at node size 8. The step's own bytes are
  at most one value node of 8 MiB at an L3 key, 16 kB, and the row and
  the table. A record that carries a step then holds at most its own
  bytes, about 42.3 MB, and one such dirty set taken whole: 1.87 GB,
  86.9 % of 2^31 - 9 at node size 8 (1.16, 1.16 and 1.69 GB at 14, 30
  and 62). So at the release's limits `recordCap()` is
  `MAX_RECORD_SIZE`, as the record limit was, and the step's room is
  there without lowering the user's limits.
* **Assumed there**, as 024-17 assumes: the count with q holds (a
  statement checked by runs, not proved: TP26 restated); H rests on V1
  (TP30, not proved). And, here: the step's last KV has at most 60
  segments (a user's key, L2, or an index entry of the Pub layer, its
  levels within L6: about 400 bytes); the row and the table together are
  at most 240 kB, which the code does not bound: the table's rows are
  removed at cuts, and the serializer's check fails the database if a
  record passes its cap (P7).
* **At lowered record limits** (tests), the cap is the record limit
  plus the step's room. Derived: the step's value nodes are at most 16 kB
  and one value node, which a transaction stored within `valueLimit()`
  and L4, so within `maxValueNode()`. Assumed: the step's index nodes
  and their got-dirty entries within `recordLimit` / 16; a record over
  its cap fails the database. The runs of section 4.3 met no such
  failure.
* **Progress** (Codex's E5): the step's allowance is the commit's
  (`fractionOf(L0 - pStart) - rewritten`, at most 16 kB), and its room
  does not depend on the transaction it rides with, so a run of maximal
  transactions cannot keep reclaim from moving; a value of the largest
  size is the first KV of a step. Checked: section 4.3, with transactions
  of 0.5 to 0.8 of the value limit in 6 % of the actions at record limits
  of 100 kB to 1 MB; the stream kept stays under the stated bound and
  does not grow from the middle third of a run to the last.
* Not derived: the take's progress at lowered limits when a dirty set
  passes the room left by every later record (005-31's case), as today.


## 4. Evidence

On F53, 2026-11-27, 11:50 to 13:10. Other work on the machine: the lead's
session and a system media analysis process at one core, load 3.5 to 5;
from about 12:40 other sessions' gates and kill tests, load up to 20.
Functional runs; times printed are figures, never a pass.

### 4.0. Gates

* `java/before-commit.sh`: `BEFORE COMMIT OK (61 s)` on `75aa41b4`
  (11:49, the first build with its tests adapted); `BEFORE COMMIT OK
  (62 s)` on `3a3d1596` (java/ as `640884b4`); `BEFORE COMMIT OK (63 s)`
  on `05d5f029`; `BEFORE COMMIT OK (73 s)` on `c5b45107`, the prototype
  as it stands (12:23). Unit 1,758 tests, f 90.
* Tests changed, each with its reason:
  * `Reclaim.Tester.testUserTransactionLeavesTimesForReclaim`: the step
    is in the commit's own record at its time: one record, the step's
    progress checked on the row; the allowance counts the stream before
    the record.
  * `testSafePosAfterTheCallsRecords`: pSafe is the marking record's own
    position (L0), with the startup pos before it at pEnd and the table
    in that record; it was the stream's length after the call's records.
  * `testCrashBeforeIterationEnd`: the last step is in the commit's own
    record; the crash comes after it (031-05: after the step's own
    record).
  * `Eviction.testReclaimWithMisses` (quick): 150 transactions instead
    of 100: with one record an action the stream reaches its first meta
    block, which the first cut waits for, at about the 100th.
  * `DbTesterFailure.testGetTransCutDuringTheWalk`: an empty commit after
    /a's record, so that the iteration's begin, in the next record, is
    before /target's record, as main's begin record after /a's was.
  * 031-05's `eagerly()` wrapper of five tests removed; no test deleted.
  * Added: `StoredValueNode.testCopyMark`,
    `Reclaim.Tester.testMaintenanceNone`,
    `Reclaim.Tester.testCopyAtAKeyTheActionWrites`.

### 4.1. Crashes, failures and stops at every record boundary

`probes/P2CrashProbe.java` (031-05's, adapted) and `probes/sweep.sh`,
031-05's configurations (its `p2crash-runs.txt`: seeds 1 to 3, 11 to 16,
21 to 24, 31 to 33 with their strides, 41), seed 3 with a restart every 7
actions of the continuation, seed 24 with one after every action, seed 41
every 3. For each record k: a crash after it (the hook throws after
`apply`), a failure after its append and before `apply` (`pre`), and a
stop after it; a start; the actions after it (a part's call ended after
its parts in the stream). Results (`sweep.sh` on the jar of `39df6831`):

* **27,720 interruptions, all continued to the uninterrupted stream**:
  9,240 crashes, 9,240 failures before `apply`, 9,240 stops; 0
  different. Every stream ended at the record's end. 23,275 of them came
  after a physical front cut. About 30 % of the records are parts of
  `maintain()` calls.
* **The start's memory was the running database's at all 27,720.**
* **Records = accepted actions** in all 23 reference runs: 16,634
  records; 10,560 commits each one record, 1,169 of them (11 %) carrying
  maintenance; the setters one record or none; 5,359 parts.
* **The review's variants** (`probes/sweep2.sh`, the variants of the
  review of 031-05's `ReviewProbe`, on the jar of `e8d85bb2`): a reader's
  `currentTime()` before every action, a refused transaction before every
  action (its key transformation throws), a clock that goes back every
  7th action, eviction at every transaction, and all four together, each
  on seven of the configurations above (seeds 2, 13, 21, 22, 24, 33, 41),
  and a clock that stands still (seed 2): 36 runs, 16,343 crashes, 16,343
  failures before `apply` and 16,343 stops, all continued to the
  uninterrupted stream, with the start's memory the running database's
  at each; records = accepted actions in all 36 (27,583 records). With
  the refused transactions and with eviction, seed 2's stream had the
  same digest as without them.
* 031-05's prototype gave the same streams at its 15,625 crashes and
  15,625 stops, with records of maintenance between the actions (031-05,
  section 7.1); here every record is an action's.

### 4.1a. Threads, then a replay

`probes/ConcProbe.java`, `probes/conc.sh` (after the review of 031-05's
`ConcProbe`): 2 to 4 writer threads, a thread of `maintain(B)` calls, a
thread of the setters, two readers at `currentTime()`, on a clock that the
threads move on; every record logged in the write lock's order with its
action and time; then one thread replays the logged actions, each at its
record's time (a part as `maintain(B, 1)`). Ten runs of 5 to 8 s, node
sizes 8, 30 and the default: 12,475 to 286,997 commits a run, up to
29,474 `maintain()` calls and 228 parts, 258 to 279 setters' records,
streams of 44 MB to 988 MB: **the replay gave the same stream in all
ten**. Where the writers did not pause (seeds 15, 19), `maintain()` gave
way to them and made 2 and 11 parts (031-04, Q9).

### 4.2. Codex's test 2: faults at four points

`probes/FaultProbe.java`, `probes/faults.sh`: six seeds, up to 8 records
of each kind (B, S, P, C, of a commit and of a part), 231 records, each
with seven injections:

| Point                         | Outcome                      | Start's memory | Continued |
|-------------------------------|------------------------------|---------------:|----------:|
| before the plan, a stop       | 231 refused, nothing written |      231 equal |  231 same |
| before the plan, an exception | 231 failed, nothing written  |      231 equal |  231 same |
| at the go point, a stop       | 231 accepted                 |      231 equal |  231 same |
| at the go point, an exception | 231 failed, nothing written  |      231 equal |  231 same |
| the append, from mid-record   | 231 torn, not accepted       |      231 equal |  231 same |
| after the append, a stop      | 231 accepted                 |      231 equal |  231 same |
| after the append, a failure   | 231 accepted, db failed      |      231 equal |  231 same |

* A refusal left the stream and reclaim's memory as they were.
* "Continued": the actions from that boundary gave the uninterrupted
  stream; for a torn record, the continuation alone and with a restart
  every 9 actions gave the same stream.
* With the tests' buffered storage, a commit whose record the storage
  then refused returned before the failure surfaced: it is not in the
  stream at the start, as `execute()`'s Javadoc says for any failure.

### 4.3. Codex's tests 1 and 3: torn tails, safety and pace

* **Torn records** (`P2CrashProbe torn`, seeds 3, 21, 41): 567 records
  cut by 1 byte, half, or all but 1 byte: each continued the same with
  and without restarts, its action not accepted, the bytes before it the
  reference's. As in 031-05 (review, F2), a torn record stays an aborted
  record: the goal holds at record boundaries.
* **Safety and pace** (`probes/SafetyProbe.java`, `PubInfoProbe.java`,
  `probes/safety.sh`): seven configurations, 3,000 to 8,000 actions each:
  cold keys put once (old live values), puts and deletes of hot keys,
  value transformations, key transformations onto cold keys, transactions
  of 0.5 to 0.8 of the value limit, `maintain()` calls, restarts; record
  limits of 100 kB, 150 kB, 200 kB (also at node size 8), 300 kB (node
  size 30), 1 MB and the release's; step reserves of 300 bytes to 4 MiB.
  * Latest and historical gets: all as the model, 5,073,567 historical
    reads at sampled times from the first available time, before and
    after 1,746 cuts and 399 restarts.
  * Provenance: 1,488,553 walks of `transactionInfo()`'s rule through
    1,978,277 copies, each ending at the model's time of the key's last
    write, or refused where that write is before the first available time;
    through the Pub API, 12,034 `transactionInfo()` calls with the put's
    time and its one KV, across 44 cuts and restarts.
  * The stream kept within the stated bound (`SafetyProbe.bound`: 2 x
    max(8 x LIVE, W / 6, 2 x SD) + 3 x W + 2 x META + 2 x CAP, from the
    design's iteration cycle; a statement, not a proof): at most 76.4 %
    of it; in six configurations its largest value in the run's last third
    was at most 1.10 times its largest in the middle third (the seventh,
    at the release's limits, refused its large transactions by L5, and its
    bound is not informative).

### 4.4. StreamDigest and RestartInvariance

As 031-05 ran them (`probes/digests.sh`, jar of `9e372dd1`):

* StreamDigest quick: "Done: 11 configurations, 4 modes; the modes give
  the same stream".
* RestartInvariance with reclaim, level3.sh's four configurations at full
  size (every1, node8, node14, node62), and level1.sh's step 5 (no
  reclaim): "STREAM: identical", the same cut, the six checks with 0
  failures, in all five.

### 4.5. 031-04's cases and the count gates

Run on the jar of `640884b4`, with 031-05's figures in brackets:

* `HoleProbe 4000 20000`: kept 71,368 bytes (71,368), the twin 52,664
  (52,664); `HoleProbe 20000 20000`: 125,976 (125,984), the twin 113,512
  (113,512). The last call that wrote: 1,605 of 10,000 (1,605).
* `IdleLiveProbe LIVE SD 20 10`, nothing written in the last 10 R in
  every case: 30,000 at 1 MB, kept 5,918 kB (5,947); 15,000, 2,954 kB
  (2,976); 100,000, 19,699 kB (19,793); 100,000 at 5 MB, 19,502 kB
  (19,604).
* `count-gates.sh all`: `COUNT GATES OK`. G1 104,828 bytes (104,560), G2
  1.229 (1.230), G3 4.303 (4.318), G4's M5 1.429 (1.933; 031-04: 1.429),
  G5's stream kept 191,240 bytes (179,456). The gates have no node size
  of their own: G1 to G4 ran at the default node size only.

### 4.5a. Read-modify-writes and the copies

031-05's `RwProbe N KEYS VALUE SD` on `c5b45107` (its label "deferred
(D1)" names the jar it runs on): 20,000 read-modify-writes of a key read
at `currentTime()`, R = 1 s: refused 0 at 200 keys of 1,000 bytes (sd
2,000; 031-05: D1 45, D2 0), 0 at 10,000 keys (sd 100,000), 0 at 100,000
keys of 100 bytes (sd 1 MB). The copies are no STM writes (rule 4).

### 4.6. The after-row charge not made

`probes/UndercountProbe.java`: a pass of `maintain()` parts, whose
records hold the step alone, so that the nodes made after the row are
the step's: over 30,000 values of 10 bytes, 25.7 % of the charge at node
size 30 (the default) and 39.5 % at node size 8; over 100,000, 25.4 % and
39.1 %. A commit's step makes the same batch beside the action's KVs,
whose nodes the record's counts cannot tell apart from the step's.
031-05 gave 6 % and 26 % from two unit tests' workloads; 028-26, 24 % to
30 % at node sizes 30 and 8. Reclaim then writes up to that much more
than its internal fraction (question Q2).

### 4.7. A figure: the time of a commit that carries a step

`probes/CommitTimeProbe.java`, 20,000 keys of 200 bytes, 30,000 commits
of one overwrite 1 ms of database time apart after 10,000 of warm-up, the
prototype against 031-05's (c315's jar, D2: the step in the commit's
call, a record of its own), two rounds each, nothing else of this work
running (load 3.5 to 4.2). Indicative only.

| Prototype          | Steps        | With a step: median, p99 | Without: median, p99 |
|--------------------|--------------|-------------------------:|---------------------:|
| 031-06, round 1    | 1,639, 5.5 % |               102, 223 us |              3.8, 31 us |
| 031-05 D2, round 1 | 1,649, 5.5 % |               114, 266 us |              3.4, 22 us |
| 031-06, round 2    | 1,639, 5.5 % |               102, 222 us |              3.8, 32 us |
| 031-05 D2, round 2 | 1,649, 5.5 % |               112, 259 us |              3.3, 22 us |

* A commit that carries a step took about 10 % less (median) and 15 %
  less (p99) than 031-05's commit with its step's record; one without a
  step about 0.4 us more at the median and 9 us more at p99: the plan
  copies the table's rows and builds its maps at every commit, also when
  nothing is due.
* Again on `c5b45107` (a plan with nothing due returns before it builds
  its KVs), at 12:46 while other sessions ran their gates and kill tests
  (load 11 to 20): with a step, medians of 113 and 115 us against 119
  and 120 us for 031-05's; without, 3.8 and 4.1 us against 3.5 and
  3.5 us; the p99s were dominated by the load (`runs/committime2.txt`).
* The user's writes become readable after the scan (transactionEnd is
  after the batch), where 031-05 and `main` publish them before the step:
  later by the scan's time, about 0.1 ms here.

### 4.8. The level scripts

* `level3.sh quick` on `3a3d1596`'s java/: steps 1 to 7 OK (the unit
  and f-tests, ReclaimStress, RestartInvariance, CrashTest,
  ReclaimReaders, PowerLossTest); step 8, the conformance, fails at its
  first check, C-STEP's fault test (`lean/test-traces/step-faults.sh`:
  16 cases wrong, "TRACECHECK FAILED: exporter" for the good traces), as
  expected (section 4.9).
* `level2.sh quick` on `c5b45107`: steps 0 to 6 OK (the pins, the unit
  tests, RestartStress, RestartInvariance, CrashTest, BryanRepro); step
  8, the tree model against Java on its reclaim set, fails: C-T5 (touch,
  92) and C-T9 (run, 150) in 5 traces, the others 0 (section 4.9).
* `level4.sh quick` on `c5b45107`: `LEVEL 4 OK` (EvictionInvariance with
  every schedule and the audit, RestartInvariance, CrashTest and
  ReclaimStress with forced schedules, ReclaimReaders, the conformance
  with eviction, LargerThanMemory).
* `apps.sh quick` on `c5b45107`: `APPS OK`, the user apps of 024-26,
  026-13 and 026-26 with their oracles (28 runs, kills of the Pub layer
  among them).

### 4.9. What fails because of the format (not attempted)

* `TraceExport` (027-02): compiles; it takes a record with a KV of
  reclaim's for a step or a table record, and a commit's record now holds
  the user's KVs and reclaim's beside them: its traces of mixed records
  have exporter errors (level3.sh, step 8).
* The trace checker's C-STEP (`TraceCheck.lean`): requires a step's
  record to hold copies and the row only; fails on mixed records
  (level3.sh, step 8, at its fault test).
* The tree model's checks of a traced transaction with a touch (C-T5)
  and of the model's own run (C-T9) (`treeconf.sh reclaim`, level2.sh,
  step 8): a traced transaction with a touch now holds the user's
  operations beside the step's.
* lean/contract's `StepTx`, `StepOpOK`: a step's transaction puts only
  old KVs met and its row (`.del _ => False`); false for a mixed record.
* Nothing was disabled.


### 4.10. A timing check against 2026.6

2026-11-27, 15:14 to 15:25: the prototype (`fa11d15f`) against release
2026.6, `timing.sh core pauses` with MINIDLE=80. The machine was 80 to
88 % idle (a process of the system held a core); a first run at the
default of 90 % was stopped by the script after three runs.

* TIMING OK.
* CORE: the median 0.255 against 2026.6's 0.260 (ratio 0.981; smaller
  is faster). The set figure 0.37 against 0.41 in each of the 4 runs of
  each build; the reads level.
* The pause probe: the longest get or commit 16.1 and 18.8 ms against
  12.2 and 15.8 ms (the guide is 50 ms). Two runs each, so the
  difference is not established.

A sanity check, not release figures: the full `timing.sh`, with the 1M
and 10M suite, runs on the ported branch.


## 5. What it costs

* **Lines of code** (`git diff -w`, comments and blank lines excluded,
  as 031-05, section 6.7, counted):
  * Against 031-04's `cfb195f3`: production +485 and -249, net +236
    (`Reclaim` +295 -199, `Db` +109 -37, `Maintenance` +22, `StoredTrans`
    +18 -3, `StoredValueNode` +17 -2, `ConnectionImp` +8 -8, `TransNodes`
    +6, `DbBuilder` +5, `Trans` +3, `Kv` +1, `NodeStream` +1); tests +229
    and -38. The study estimated +200 to +280.
  * Against 031-05's `4135ba2a`: production +450 and -403, net +47
    (`Reclaim` +272 -254, `Db` +97 -101, `DbClock` -34, the rest as
    above); tests +223 and -56.
  * By part, net against `cfb195f3`, about: reclaim's plan and apply
    (`RecordPlan`, `plan`, `planCommit`, `planPart`, `finishPlan`,
    `apply`, `applyCut`, the step's copies, `planSafe`, `planCut`, less
    `transactionCompleted`, the step's transaction, `storeTable`,
    `storeCurrent`, `markSafePositions`, `pretruncateIfPossible`) +96;
    Db's path (`planMaintenance`, the admission, `merge`, the plan's
    fields of the record, `apply`'s call, `maintainPart` replacing the
    part's own loop) +68; the interface +22; the copy mark +23
    (`StoredValueNode`, `TransNodes`, the serializer and Db's line;
    `transactionInfo()` net 0); the step's room +19 (`StoredTrans`,
    `Trans.recordCap`, `NodeStream`, the take); the actions' flags
    (`Trans.part`, `noMaintenance`, `Kv.planned`) +3; the empty
    implementation's builder setting +5.
* **New state in memory**: none in Reclaim but `RecordPlan`, which lives
  for one record; `Trans.part`, `noMaintenance`, `recordCap`;
  `Kv.planned`; `TransNodes.copyKeys`; `ExecuteData.plan`. Removed:
  031-05's `lastIsTrigger`, `lastEnd`, `lastTime`, the hold and the call's
  time.
* **New state in the stream**: the copy mark, byte 6 of a value node.
  The rows' a is a commit's own position when its record stores them.
  Records of reclaim's own are written by parts only.
* **Recovery cases**: none. A start writes nothing.
* **The format**: the copy mark (a stream that 2026.6 or `main` reads
  misreads a mixed record; question Q5); one record an action changes
  every stream's bytes from the first step on.
* **P1**: section 4.7. The write lock is held through the scan, as on
  `main`; readers see the commit after the scan.


## 6. Open questions for Frans

* **Q1. A1: take (e)?**
  * Options: (a) (e) as built; (b) (c), the fallback (031-05's D2 and a
    start that writes what is due); (c) (d), the compound unit.
  * Recommended: **(a)**. Every probe of 031-05 and the three tests that
    Codex named pass on it, with fewer mechanisms than 031-05's (no
    catch-up, no trigger, no hold, no start that writes, nothing between
    records), at +47 lines net over 031-05's prototype. Its costs: the
    copy mark (a format change), the trace format and the contract model
    of a step to restate, readers that see a commit after its scan.
* **Q2. The after-row charge** (rule 12; 028-26; 031-05, Q3).
  * Options: (a) not made, as built: reclaim writes up to 25 % (node
    size 30) to 39 % (node size 8) more than its fraction in a pass of
    small values; (b) a deterministic estimate of the batch's nodes,
    stored in the row; (c) the step charged with its record's index
    bytes, in the next record (the lag of one record): exact for a part's
    record, an over-charge for a commit's, whose index bytes are also the
    action's.
  * Recommended: **(b)**, as a 028 entry before the landing, gated by G1
    to G4; (a) for the prototype.
* **Q3. The step's room** (rule 5).
  * Options: (a) on top of the transaction's limits, as built, with the
    record cap at the format's limit at the release's limits; (b) the
    transaction's internal limits lowered so that the room is reserved at
    the release's limits too (a record limit of 15/16 or 16/17 of the
    format's: 024-17's worst record, 1.51 GB at node size 8, fits either);
    (c) the step sized to the room the transaction leaves (the study's
    rule 4), which Codex's E5 shows can starve reclaim.
  * Recommended: **(a)**, with section 3's derivation written into
    024-17's bound when the design lands.
* **Q4. The 1,024 kept times and top node ordinals** (015-55, 005-02):
  nothing runs after a commit any more. Options: (a) removed, as their
  own change after the landing; (b) kept. Recommended: **(a)** (the
  study's question E5).
* **Q5. The format's version for the copy mark**: (a) a new version of
  the value node (5 to 6) and of the meta block, so that 2026.6 refuses a
  stream with mixed records before it writes; (b) the meta block's only;
  (c) none. Recommended: **(b)**, with A3's rule for streams of 2026.6.
* **Q6. The cost of the plan at every commit** (section 4.7): about
  0.4 us at the median. Options: (a) as built; (b) a cheap first test on
  the live rows, copied only when something is due. Recommended: **(b)**
  at the landing, if a timing run (`timing.sh`) shows the cost.


## 7. State

2026-11-27, 13:10.

* **Done:** the prototype (branch `031-06` of the clone, outside the
  repository), with `BEFORE COMMIT OK`; the probes and their runs of
  section 4; `prototype.diff` (java/ against `4135ba2a`).
* **Not done:** night.sh, week.sh, `timing.sh`, level2.sh and level4.sh
  in full, `apps.sh` soak and kill rounds, the 10M-key runs of 031-04;
  the count gates at node size 8 (they have no such setting); an
  independent review of the prototype.
* **Next:** Codex's review of the prototype; Frans's decision on A1 and
  Q1 to Q6.


## 8. The decision on A1, and Frans's answers

Frans, 2026-11-27:

* **A1 is (e), one record an action.**
  * 13:53: the review by an agent on Fable is enough to go on, if it is
    ok; Codex's review is not needed for it.
  * 14:30: the review's verdict (`review-fable.md`): no probe broke the
    prototype, and (e) is the one for `main`, after three fixes (the
    conformance, the record's room by a check, the pace). With that, A1
    is (e).
  * Codex's review of the prototype was stopped by OpenAI's content
    filter at 14:24, after about three minutes of work, and gave no
    report. It was not reworded or tried again (013-04, section 9).
* **The prototype's three problems** (14:00 to 14:09), none a blocker:
  * that readers see a commit after its scan is not a problem;
  * the record's size needs no formal bound: that it works in practice,
    with enough testing, is enough; a guarantee that is cheap is welcome
    (Q3);
  * the after-row charge (Q2): the fixed-width patch of the row is tried
    first: the row's number at a fixed width, filled in after the batch
    is built and before the record is appended, so that the charge is
    exact in one record (031-05's review, F8). Later, not a blocker; the
    fallback is the charge one record later (Q2 (c)).

Q1 is answered by this. Q4 to Q6 are steps of the landing (section 9).

* **A2** (14:36): `maintain(int budget)` replaces `maintain()` in the
  Core and the Pub API in 2026.7.
* **A3** (14:36): 2026.7 does not open a database of 2026.6: a new
  format version, refused with a clear message; no upgrade path.
* **028-67** (15:50 to 16:02): its C1 and C3 are built in this landing,
  with the format's other changes (section 9, step 4).


## 9. The landing

The steps, each with what it is and its gate. An agent of lead-1127
began steps 0 and 1 in a clone on 2026-11-27, 14:32.

0. **The port.** The prototype's Java on `main` of 2026-11-27, after
   028-69 (the crypto code removed) and 028-60's part 2, on a branch.
   Gate: `BEFORE COMMIT OK`.
1. **The conformance** (the review's F1): the trace format (027-02) with
   the copy mark, `TraceExport`, C-STEP with its fault test, C-T5 and
   C-T9, and the contract's `StepTx`. Gate: `level2.sh`, `level3.sh` and
   the contract's `gate.sh`, whole.
2. **The record's room by a check** (F5, F6, F7): the admission counts
   the step's nodes, or the transaction's limits leave the room (15/16 of
   the format's limit, Q3 (b)); the Core bounds its own long keys; the
   step reserve (028-68).
3. **The pace** (F2, F3, F4): the after-row charge by the fixed-width
   patch (section 8); a commit's step sized by its allowance under large
   commits (028-71); a warm-up of the step's scan before the lock; P1
   measured on a database larger than memory.
4. **Clean-up:** the 1,024 kept times and top node ordinals (Q4); the
   meta block's or the format's version for the copy mark (Q5), with
   028-67's ties in the same format: a meta block's own position and its
   database ID checked, and a record header's 24-bit check of the ID, its
   position and its fields; the tests that depend on the stream's layout.
5. **The documents:** 027, 027-02, 027-03, the Javadoc of
   `maintain(budget)`, the README's sentence on the same bytes; P2 in
   010, by Frans.
6. **The hunt:** user applications with kills on the new code,
   `night.sh`, `week.sh`, `timing.sh`, and a review of the landed diff by
   an agent on Fable.

The branch is merged into `main` (`--no-ff`) when steps 0 to 2 are green;
steps 3 to 6 are made on `main`.

The two points that waited for Frans's word before the merge, A2 and A3
(the public API and the stream format), were decided on 2026-11-27 at
14:36 (section 8).


## Log

2026-11-27. Created by lead-1127 from Frans's decision of 11:18: a
prototype of one record an action (A1's (e)), on 031-05's. Built by an
agent of lead-1127 in a clone, 11:20 to 13:10: the prototype, with
`BEFORE COMMIT OK`; 27,720 crashes, failures and stops at record
boundaries continued to the uninterrupted stream, and 49,029 more with the
review's variants, with the start's memory the running database's at
each, and as many records as accepted actions; ten runs of threads
replayed to the same stream; Codex's three tests (torn records, faults at
four points, safety and pace with transactionInfo through copies);
StreamDigest, RestartInvariance, 031-04's probes, the count gates, the
quick level scripts and apps; the after-row charge measured; a figure of
the commit time; `study.md` (the study of (e), as written that morning).

2026-11-27. The independent review of the prototype by an agent on Fable
(13:10 to 14:30, `review-fable.md`): no probe broke it; F1 to F9, of
cost, margin and scope; (e) for `main` after three fixes. Codex's review
was stopped by OpenAI's content filter, with no report. A1 is (e)
(Frans; section 8). The item's files landed on `main` from the clones;
the landing's plan is section 9, and its steps 0 and 1 began.

2026-11-27. A2 and A3 decided by Frans (14:36; section 8). A timing check
of the prototype against 2026.6 (section 4.10): TIMING OK, a sanity check.
028-67's C1 and C3 join the landing's step 4 (Frans, 16:02).
