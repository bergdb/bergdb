# A1 (e): a commit's maintenance inside the user's record

A feasibility study, 2026-11-27, 09:44 to 11:15, by an agent of
lead-1127, for 006-37's question A1, option (e): the maintenance that a
commit owes is written in the user transaction's own record. Read: 031-05
(sections 2, 4, 6, 8, 9, 10, 12 and review-fable.md), 031-04, 006-37,
028-54, 028-26, 010-01 (P1, P2, P3, P7), 027-03 (section 8), 027-13,
024-17 (section 5), the history of reclaim's records
(history-separate-records.md), and the prototype's code, branch `031-05`
at `4135ba2a` (`java/` at `8a6bb105`), in a clone (branch `a1-one`, outside the
repository). Each statement is
marked **ran** (run here), **read** (code or text read) or **inferred**.
Option (d), the compound unit, is studied elsewhere; where an obstacle
would not exist for it, one line says so ("(d):").

One probe was written and run: `probes-a1/OneRecordProbe.java` in that
clone, with its output in `probes-a1/one-record-runs.txt` (neither is in the
repository). It runs 031-05's
prototype eagerly (D2, where a commit's maintenance follows its record in
its call, as on `main`) and sizes what merging that maintenance into the
next user record would meet: six workloads of 3,000 to 20,000 commits, 20
to 5,000 keys, values to 30 kB, node sizes 8 and the default, startup
distances 2 kB to 50 kB, R = 1 s.


## Verdict

**Feasible, with three warts; clean in its mechanism.**

* **The mechanism is simpler than every variant of 031-05.** One action,
  one record: a commit's record holds its transaction and the maintenance
  decided from the stream before the record. Nothing is ever due between
  two records, so the catch-up, the trigger, the held clock, the D1/D2
  switch, Q8's refused call that writes, and a start that writes (Q2 (c))
  are not needed. A crash or a stop at any record boundary lies between
  two actions, and a torn record is recovered as today: both the user's
  writes and the maintenance, or neither. In the Lean model a commit is
  one transaction, so `T1_crash`, `T2_restart` and `T12_restartCut` hold
  as they are. The price is a lag of one record: a decision that reads a
  record's own length or take (a begin or a step from its growth, the
  safe positions from its take) is made in the next record, a commit's or
  a `maintain()` part's (point 1).
* **Every quantity that today names the user record's own end can be
  decided before the record** (point 1): the begin's pStart and the last
  step's pEnd and the safe position pSafe become the record's start; tStart
  becomes the last record's time and tEnd the record's own time. The one
  exception is 028-26's after-row charge, which no record can hold of
  itself.
* **The warts:**
  1. **A copy mark in the format.** A user record that carries a step
     holds the user's KVs and reclaim's copies side by side, and nothing
     in the record tells them apart today. `transactionInfo()` (005-42,
     021-17) would throw `InternalDataException` for the user's own
     values in every commit that carries a step, and give reclaim's
     copies as the user's KVs. The fix is a flag on a copy's value node
     (027-03, section 8): a format change. Backwards compatibility does
     not count (Frans, 2026-11-27, 09:38).
  2. **The after-row charge stays dropped** (028-26; 031-05, Q3 and F8):
     the step's row charges its value bytes and the nodes its touch made
     dirty, not the nodes that the record's batch makes afterwards.
     Reclaim may write about 6 % more than its fraction at the default
     node size and 26 % more at node size 8 (031-05, section 6.5). Option
     (c) has the same wart.
  3. **A larger rework than option (c).** Reclaim stops writing
     transactions of its own after a commit: it plans KVs for the
     record, and applies the plan to its memory after the record is
     appended. The trace format (027-02), the trace checker's C-STEP and
     the contract package's model of a step (`StepTx`, with Mathlib)
     change. 024-17's bound on a record's size is derived again with the
     step's share. The estimate is about +200 to +280 lines of production
     code over 031-04's prototype, against about +135 to +155 for (c)
     (point 7).
* **Nothing found breaks it outright** (point 9). Two things break it if
  they are left as they are: `transactionInfo()` (wart 1), and the start's
  reading of a, `appA`, which would differ from the running database's
  after a mixed record. Both are fixed by the copy mark.


## 1. What a commit's maintenance writes, and the self-reference

**On `main`** (read: 027-13, sections 1.2 to 1.6; 028-26), after the user
record, under the write lock, in the same call
(`Db.executeLocked` → `Reclaim.transactionCompleted`), each a record of
its own, an internal transaction at a time of its own (from the clock):

* **B**, the begin: the table `/#i/dreclaim/-table.txt` with a new row:
  pStart = L, the stream's length after the user record; tStart = t, the
  user's time; pCut; E = the last key live at t (`lastKeyAt`).
* **S**, a step: copies of the old live KVs (`putLongKey` with `keyRead`
  at the scan's time), the current row `/#i/dreclaim/-current.txt` (a
  value transformation that reads `Trans.dirtiedBytes` after the touch),
  `touch = true` for the whole transaction. Its allowance is
  `fractionOf(L - pStart) - rewritten`.
* **S'**, the row again (028-26): the bytes that the step's batch made
  dirty after the row was made, in a record of its own.
* **E**, after the last step: the table with done, tEnd = the step's
  time and pEnd = the step's position, in a record of its own.
* **P**, the safe positions: the table with pSafe = the stream's length
  after this call's internal records (015-54).
* **C**, the cut's decision: the table (rows removed, the row marked
  cut), at now = t; in memory fa, fp, the pending cut, the caches dropped
  (026-10).
* Up to six internal records after a user record (028-26).

**In the prototype** (read: `Reclaim.catchUp`, `commitWork`,
`markSafePositions`, `pretruncateIfPossible`, `step`): the same B or S, P
and C, decided from the stream's last record (`lastIsTrigger`, `lastEnd`,
`lastTime`, kept by `recordWritten` and read by `initFromDb`), timed from
the last record (`DbClock.maintenanceBegin`); S' and E are gone, and the
last step's row holds done, tEnd = its record's time and pEnd = its
record's start. Ran (the probe, D2): maintenance follows 5 % to 30 % of
the commits, at most 3 records after one.

**The self-reference.** Each of these reads the user record's own end or
time:

* B: its condition `lastEnd > lastPStart + 2 sd` and pStart = lastEnd;
  tStart = lastTime; E at lastTime.
* S: the allowance from lastEnd; its scan at the state after the user's
  record.
* P: pSafe = the length after the call's records; its condition
  `sp >= pEnd` with sp after their takes.
* C: now = lastTime; sp and mp after the call's records.
* The last step: tEnd and pEnd of its own record.
* S': the bytes of its own record's batch.

**Each can be decided from the stream before the record** (inferred,
from the code read):

* **L0**, the stream's length before the record, replaces lastEnd. B's
  condition, S's allowance and B's pStart use L0. pStart = L0 keeps the
  rule that every record before pStart was written at or before tStart.
* **tStart is the last record's time**, the time of the state at L0, and
  E is the last key live then. This is the convention that `maintain()`'s
  M1 already uses (`maintainPart`: pStart = the stream length, tStart =
  the last transaction's time), and the contract package's (`StepsOK`:
  "E the greatest key live after t0", pCut at most t0 + 1). A value stored
  before L0 and live at tEnd was live, with that value, at tStart.
* **The step scans the state before the record**, which is the state that
  `main`'s step after the previous user record scans. Its copies are the
  values just before the record's time.
* **pEnd = L0, pSafe = L0, tEnd = the record's time tt, now = tt.** The
  prototype already sets pEnd to the record's start (`stepPos`). For
  pSafe, 015-54's reason is that pSafe must come after the records whose
  takes moved sp past pEnd and kept nodes dirty (the class comment of
  `Reclaim`). With sp read before the record, those records are all
  before L0. A node that this record's own take keeps dirty has its
  record at pSafe, as on `main`, where pSafe is the position of P's own
  record.
* **sp and mp** are those that the last record left.
* **Order:** B, P and C are evaluated in that order on the state before
  the record. B and S exclude each other (the allowance at B is 0). The
  row that S makes done has pEnd = L0, which is above sp, so P cannot mark
  it in the same record. A row that P marks has pSafe = L0, which is above
  sp, so C cannot cut it in the same record. So no decision depends on
  another one in the same record. On `main` the same holds within a call.
* **S', the after-row charge, cannot be decided before:** the row is a
  value of the record whose batch makes the nodes (028-26, Decision, D
  and E). In one record the batch also holds the user's puts. Not
  charged (wart 2).

**A lag of one record, not a due state** (inferred). The growth and the
take of record k count from record k + 1 on. What `main` writes after the
application's last commit and that depends on that commit's own bytes or
take (a begin or a step from its growth, a P from its take) waits for the
next record, a commit or a `maintain()` part. A cut whose conditions held
before the record is decided in it, at its own time. There is no clock to
hold and no record that a call or a start must write for another.
(d): no lag; the unit's records follow the user's, as on `main`.


## 2. The record limit

* **The limits** (read: `StoredTrans`, `Db`'s Javadoc, 024-17): the
  record limit is 2^31 - 9 bytes, not 8 MiB. 8 MiB is L4, a value. A
  user transaction has at most 500 operations (L1), 56 KiB of keys (L3)
  and 32 MiB of keys and values (L5). A record's value nodes take at
  most 7/8 of the record limit (`valueLimit`), and a transaction's dirty
  nodes at most 15/16 (`dirtyLimit`).
* **A step's share** (read: `Reclaim.step`; 024-17, 5.5): at most
  `MAX_STEP` (16,000 bytes of what it counts) and one more KV of up to
  L4, plus its row. Its dirty nodes are those on the paths of its puts,
  at most the nodes its scan followed (`maxNodes = RESERVE / NB`, about
  4 MiB of nodes), plus the writer's replacements.
* **At the release limits it never binds** (inferred from 024-17,
  section 5.3). The worst record, at node size 8, is 1.51 GB, 70.2 % of
  2^31 - 9. Adding a step of about 8 MiB of values and 8 MiB of dirty
  nodes gives about 1.52 GB, about 71 %. The bound has to be derived
  again with the step's term (an obligation in 024-17 and in the model's
  `Limits.release`), but the room is there.
* **At the tests' lowered limits** a merged record can pass (read):
  * `LimitsTester` runs with reclaim on (R = 1 s) and eviction, at record
    limits of 240 kB, 300 kB and 1 MB, with values whose nodes take the
    value limit and a few bytes more or less, and checks that a
    transaction within the limits is committed. So it exercises the rule
    below.
  * `DbTester`'s four lowered-limit tests (100 kB to 1 MB) set no retain
    duration in the lines read around them.

  Rule: the plan sizes the step to the room the user's transaction
  leaves:
  * the step stops before a KV whose value nodes would pass `valueLimit`
    less the user's value bytes. Unlike 015-50's step, the first KV is
    not admitted unconditionally: if it does not fit, the record carries
    no step;
  * the record carries no step if the user's dirty-node count
    (`checkDirtyNodes`'s) plus the step's bound passes `dirtyLimit`.
* **Less maintenance, or none, keeps both rules** (inferred). The room
  is a function of the action (its KVs) and of the stream (the count
  reads the tree), so the goal "a function of the stream and the
  actions" holds. Reclaim's pace is already bounded per commit:
  `min(allowed, MAX_STEP)`, so a large allowance waits for later commits
  anyway. A skipped step is taken by the next commit that leaves room,
  or by a `maintain()` part, which has the record to itself. At the
  release limits no step is skipped.
* **Ran:** in the six workloads the largest merged record (user record
  k + 1 and the maintenance after k) is 38,088 bytes where the largest
  user record is 31,896; at most 2.2 times (36,944 against 16,584, 300-byte
  values, sd 20 kB).
* (d): no shared limit; each record of the unit is sized as today.


## 3. One key, two writers; the scan; the STM; transformations; admission

* **The user's key in the step's range** (ran, the probe). These are the
  copies that the step after record k makes and that user record k + 1
  writes: the copies that one record drops. Per workload, as a share of
  the copies (and of the steps):
  * 200 keys: 0.65 % (3.3 % of the steps);
  * 200 keys, 60 % multi-key puts: 1.07 % (5.4 %);
  * 20 keys, 60 % multi-key puts: 9.04 % (11.9 %);
  * 5,000 keys of 300 bytes: 0.04 % (0.9 %);
  * 2,000 keys at node size 8: 0.14 % (0.8 %);
  * 200 keys of up to 30 kB: 0.37 % (0.5 %).
  As a check, the copies that the step after k makes of keys that record
  k itself writes: 0 in every run.
  * **Rule:** the user's write wins and the copy is dropped. The user's
    put makes a new value node at the record (at L0 or later, so after
    pStart), and the user's delete leaves no live value. Either way the
    key needs no copy. The step's lastKey and kvCount stay as the scan
    left them, and rewritten counts only the copies kept (inferred,
    `Reclaim.step`).
* **The scan** (read: `step`, `GetMany` at `Long.MAX_VALUE`). On `main`
  the scan reads the state after the user record. In one record it runs
  before the user's operations are applied, under the write lock, after
  the user's checks: the state after the previous record. The coverage
  argument (023-05, P8; `step`'s Javadoc) holds with "the state before
  the step's record" in place of "the step's time", as the contract model
  already states it (`StepTx`: "a put of every old KV met ... with their
  values immediately before the step").
* **The STM** (read: `stmCheckConflicts`, `stmRecordKeys`, `step`). The
  step was an optimistic transaction: `keyRead` at the scan's time, and
  dropped on `RerunException`. Under the write lock it cannot conflict
  (027-13, 1.4.4, argued). In one record the copies are reads under the
  lock, not STM reads: no `readKeyHashes`, no rerun case. A copy changes
  no value. Recording its key as written (`keyModSet`) is only needed to
  refuse readers that a copy cannot harm, so the copies are left out of
  `writeKeyHashes` (inferred). This also removes the reruns that D1 caused
  (031-05, section 8: 45 of 20,000 read-modify-writes refused).
* **Key transformations** (024-16, `transformKeys`) run first, and the
  plan merges after them. Two KVs at one key cannot come from the merge,
  as user keys are dropped from the copies. Reclaim's keys are core keys,
  which a user transaction and its transformations cannot write
  (`checkCoreKeys`, 024-37), so the row and the table never meet a user's
  KV.
* **Value transformations.** The user's run before the go point
  (`transformValues`, 026-06), reading the value before the transaction.
  The row's and the table's run in `putKvs`, today only for internal
  transactions (`kv.valueTransformation != null &&
  x.trans.isInternal()`). This becomes a flag on the KV (the existing
  `coreWrite`, or one of its own). The table, when the record also holds
  a step (S with P, or S with C, both possible), is made the same way, so
  that its row of the running iteration has the step's charge.
* **The touch** (read: `putKvs`, `touchPaths`) is one flag for the whole
  transaction and walks every KV. It becomes a list of keys, the
  copies'. The row's charge is then the touch's dirty bytes, measured
  before the batch. They are counted against the same D as on `main`
  (the D after the previous record), so the charge is the same as
  `main`'s step's (inferred).
* **The admission count** (RB-005, 028-45, 028-50: `checkDirtyNodes`,
  `checkDirtyNodesAfterKeyTransformations`) counts the user's keys after
  their transformations, unchanged. The plan adds the step's bound and
  skips the step if the sum passes (point 2). Ran: the largest got-dirty
  list of a merged record is 18 to 76 nodes (76 at node size 8, where the
  largest user record's is 44 and a step's 41).
* (d): no collision, no shared touch or STM, and the step stays a
  transaction of its own.


## 4. What depends on "one record, one user transaction"

* **`Db.getTrans`** (read): it returns a record's nodes, unchanged. The
  only production caller is the Pub layer's `transactionInfo()`. The
  Core apps' chain walk (`stress/apps/a2-churn/Churn.java`: back from a
  record to `tt - 1` until the write time) works by times and needs no
  change. RB-008's and RB-009's walk to a record's start is in the
  record's framing, which does not change (inferred).
* **`transactionInfo()`** (read: `ConnectionImp.transactionInfoInner`,
  `isReclaims`):
  * As written, it breaks. A record with a KV under `/#i/dreclaim/` is
    taken for a step, and every value of it is followed back to `tt - 1`.
    For the user's own new value in a mixed record, the value before is
    another one, so it throws `InternalDataException` ("not a copy").
    This would happen in every commit that carries a step: 5 % to 25 %
    of the commits in the probe's six runs (ran: 427 to 1,008 steps a
    run).
  * The KV list would include reclaim's copies as the user's.
  * Needed: a copy mark, a flag on the value node. Its header has spare
    bytes: bytes 6 and 7 of a value node are zero, and the parser skips
    them (`StoredValueNode`, its class comment and `parse`; read). With
    the mark, `transactionInfo()` follows a value back only if its node
    is a copy, and lists the user's KVs without the copies. The time is
    the record's, the user's.
* **The kept times and top node ordinals** (read: `DbClock.
  transactionBegin(!isInternal)`, 015-55; `TOP_ORDINAL_MARGIN`, 005-02):
  1,024 each, kept for the internal records after a user record. In one
  record a commit's maintenance takes neither a time nor an ordinal of
  its own. `maintain()` parts and the setters are refused as user
  transactions are (`refuseIfTopOrdinalsUsed`), so both margins can go
  (inferred).
* **`Trans.maintenance`, `DbClock.maintenanceBegin`, `DbClock.hold`,
  `DbClock.actionTime`** (the prototype's): not needed, when each record,
  a `maintain()` part's too, takes its time from `transactionBegin`
  (inferred).
* **The Pub layer** commits through `Db.execute`. Its index jobs' commits
  (N9) carry maintenance like any commit, as on `main`. The only
  dependency is `transactionInfo()` (read).
* **`appA`** (031-04's a; read: `recordWritten`, `initFromDb`,
  `isOwnRecord`). The running database sets a at every user record. A
  start takes the last record as reclaim's own if it holds a reclaim key,
  which a mixed record does, so it reads a from the row: another a than
  the running database's, which breaks restart invariance. The rule is
  made one function of the record, used in both places: a record is
  reclaim's own if every KV in it is a copy or a reclaim key. An empty
  commit that carries maintenance then counts as reclaim's own, where on
  `main` it counts as the application's. That changes only when M1
  begins a pass.
* **TraceExport and the trace format 027-02** (read: `TraceExport`,
  kinds `user`, `step` and `table`; "not the first of its call"). The
  trace becomes simpler: a call's record is always its own. A user
  record may carry a STEP and a TOUCH line, and its TX line marks the
  copies. `crash=K` ("after every K-th step") crashes after a user
  record.
* **The contract checkers** (read: `TraceCheck.lean`, C-STEP;
  `Contract/ReclaimSteps.lean`, `StepTx`, `StepOpOK`):
  * STEP-ops and STEP-puts require a step's record to hold only copies
    and the row. They are restated for the copies, by the mark, with the
    user's operations allowed beside them on other keys.
  * C-CUT (the RC checks) is per record and unchanged.
  * 001-07's mapping, "zero to five internal records between user
    transactions", becomes none after a commit.
* **StreamDigest and RestartInvariance**: unchanged code; their digests
  change (inferred).
* (d): `transactionInfo()`, `appA` and the trace keep separate records.
  The unit's mark is a new input to them instead.


## 5. Refusal after the go point

* **One record** (inferred from `executeLocked`'s order, read):
  * Every refusal of the user's transaction comes first, from its own
    checks, all before the go point: the size, the ordinals, the dirty
    count, the STM, the key and value transformations.
  * The plan comes after the last of them, still before the go point.
    It reads only; it changes nothing but the cache.
  * Nothing refuses the maintenance. It is sized to fit (point 2), and
    it takes no time or ordinal of its own.
  * An exception in the plan fails the database (P7). The plan runs
    inside a `catch (Throwable e) { throw fail(t, e); }`, as
    `checkDirtyNodesAfterKeyTransformations` does, and a read that fails
    on the storage fails the database by itself.
  * A `stop()` that refuses a maintenance read before the go point
    refuses the user's transaction, with nothing written. The call throws
    and is not accepted.
  * After the go point, any failure fails the database. The record is
    appended whole or not at all, and a torn one is recovered as today.
  * So the outcome is one of three: refused with nothing changed;
    committed with its maintenance; or failed, with the record wholly in
    the stream or not at all.
* **`main`** (read): the maintenance runs after the go point. A failure
  fails the database (015-50 was such a case), and a stop during it
  leaves the user committed and the maintenance for later (015-53). That
  is 028-54's case.
* **The prototype** (031-05, F7, Q8): the catch-up runs before the user's
  checks, outside the code that fails the database. A refusal after it
  leaves maintenance records written for a refused call (Q8) and memory
  ahead of the stream.
* One record has neither case.


## 6. P1

**Confirmed, as an inference; not measured.**

* The same work runs in the same call under the same lock: the scan,
  the copies, the row, the table, the take (read: `executeLocked`,
  `transactionCompleted`).
* One record has fewer headers, one take instead of up to seven (the
  user's and up to six internal records on `main`), and one top node
  instead of up to seven. Each of these is less work.
* What moves: readers see the user's writes after the step's scan
  instead of before it (`dbClock.transactionEnd` is after `putKvs`). The
  delay is at most the scan of about 16 kB of KVs, or a 4 MiB node
  reserve with a cold cache, as on `main` before the call returns. It is
  later freshness, not a wait: readers read at earlier times and never
  wait for the writer.
* A step that copies a value of 8 MiB holds the lock 65 to 155 ms
  (024-17, section 1), today as well.
* Not measured: `timing.sh`, the pause probe.


## 7. What goes from the prototype, what is added, and the size

**Goes** (read: 031-05, section 6.7, and the prototype's code):

* `catchUp`, `catchUpRecord`, the trigger (`isTrigger`, `lastIsTrigger`,
  `lastEnd`, `lastTime`): about 60 lines.
* The predicates `catchUpDue`, `safeDue`, `cutDue` and the split of
  `pretruncateIfPossible`: about 35 lines.
* The hold and the maintenance times (`DbClock.hold`, `holdIfDue`,
  `maintainCalls`, `maintenanceBegin`, `actionTime`,
  `Trans.maintenance`): about 60 lines.
* The D1/D2 switch and the setters' and `maintain()`'s catch-ups: about
  20 lines.
* Q8, F3, F5, F6, F7 and F1 as questions:
  * F1, a setter deciding a cut: setters carry no maintenance, so a
    setter behaves as on `main` (inferred);
  * F7: point 5.
* Also gone, from `main`: the listener call and its
  `DbStoppingException` catch (015-53) in `executeLocked`, and reclaim's
  nested `db.execute` of steps and tables after a commit. `storeTable`,
  `storeCurrent` and the step's `Trans` become KVs of a plan.
* About 175 of the prototype's 231 added lines go.

**Stays:** one record a `maintain()` part (about 25 lines); the done row
in the step (about 10 net); `maintain(int, int)` for probes.

**Added** (inferred):

* `Reclaim.plan` and `Reclaim.apply`, about 100 to 140 lines changed or
  added:
  * the step split into its scan and its KVs;
  * B, P and C producing the table's next state;
  * the memory effects (rows, fa, fp, the pending cut, `cutDecided`)
    after the record;
  * the room rule of point 2.
* `Db.executeLocked`, about 50 to 70 lines: the plan after
  `transformValues`, inside the failing code; the merge (drop the user's
  keys from the copies, sort); the touch and the value transformations
  by KV; `apply` after `store()`.
* A `maintain()` part through the same path (an empty action and the
  part's plan): about 20 to 30 lines.
* The copy mark in `StoredValueNode`, its parse and `StoredTrans`:
  about 20 to 30 lines.
* `transactionInfo()`: about 10 lines; `isOwnRecord`: about 5.

**Net, production:** about +200 to +280 lines over 031-04's prototype.
For **(c)**, the reviewer's variant (review-fable.md, F6): the
prototype's 231 lines, less 80 to 100, plus about 4 in the start, so
about +135 to +155. One record thus has about 1.5 to 2 times (c)'s lines,
but fewer mechanisms: no catch-up at four sites, no "would write"
predicates kept alike by hand (F7), no hold, no start that writes, and
reclaim never calls `execute` after a commit.

**Tests** (inferred):

* Reclaim's tests that look at a commit's internal records: the five
  that `eagerly()` runs (031-05, section 6.6) and those that count
  records by kind. Also `TraceExport` and the trace checker's fixtures.
* About 150 to 300 lines changed. (c) keeps most tests as the prototype
  has them.

**Lean** (point 8):

* lean/SIS: no change.
* A policy theorem: about 100 to 300 lines, against the sketch's 600 to
  1,100 (031-05, section 9; review, answer 6).
* lean/contract's `StepTx`: about 50 to 200 lines, with Mathlib.
* The checker: about 30 to 60 lines.


## 8. The Lean model

* **lean/SIS** (read: `Algorithm.lean`, `step`; `Reclaim.lean`):
  * `step` appends one record a transaction. Its change is computed
    from the view of the state before it (`sp.exec tr i (view sp db.P
    (i - 1))`), and the touch is `Changes.touch`, a list of nodes per
    transaction.
  * A commit with its maintenance is one `T`, whose changes are the
    user's and the copies' and whose touch is the step's paths.
  * `T1_crash` (a crash leaves a prefix of whole records),
    `T2_restart`, `T12_restartCut` and `full_restart` and `full_cut`
    (contract) apply to such lists as they are. Nothing in lean/SIS
    changes. The first available time per record (`faPolicy S D i tr`)
    may already depend on the record's own transaction, which a cut
    decided in a commit's record needs.
* **What is proved as is:** for any list of records, mixed ones
  included, a crash at a record boundary and a restart change no record.
  With one record per action, a crash at a boundary falls between two
  actions.
* **What remains to state:** the list is chosen by Java's policy. Each
  action a gives one transaction, `plan S a`, from what a start restores
  of S. The theorem: a run of the accepted actions with crashes and
  restarts at record boundaries gives the uninterrupted run's stream. It
  follows by induction from `T2_strong` (Proof/Restart.lean) and
  `restartCut_rel` (Proof/CutRuns.lean), with one hypothesis: that `plan` depends only on
  what `Rel` preserves (inferred). The sketch's `DueMono`, `DueEnds` and
  `MaintPrefix` are not needed, nor the corrected equality of F3. A
  `maintain()` part is an action of its own (F4's suggestion). That
  Java's plan is such a function stays tested, as in every variant.
  About 100 to 300 lines without Mathlib.
* **lean/contract** (read: `Contract/ReclaimSteps.lean`):
  * `StepTx` requires that a step's transaction puts only old KVs met
    and its row (`StepOpOK`: `.del _ => False`; a put is the row or an
    old KV met). This is false for a mixed record.
  * The change: a transaction's operations are the action's and the
    step's, on disjoint keys. `StepOpOK` constrains the step's. "Every
    old KV met is put again" becomes "is put again by the step or
    written by the action".
  * `iterationOK_of_stepsOK` then needs, for the second case, that the
    action's write makes a new node (`MeetsFull.made_once`) or deletes
    the key.
  * Reclaim's preservation theorem (reclaim changes no user value) is
    restated over the step's operations only.
  * The model's convention already matches one record: "Step st is the
    transaction st.j + 1 ... its scan reads ... the tree after
    transaction st.j". About 50 to 200 lines, with Mathlib (`gate.sh`).
    Not read in full.
* **TraceCheck / contractcheck:** C-STEP reads the copy mark from the TX
  lines (about 30 to 60 lines). C-CUT is unchanged.
* (d): lean/SIS sees several records per unit. That a start drops an
  incomplete unit is an assumption to test (006-37, 09:40), and
  lean/contract is unchanged.


## 9. Attempts to break it

Each was tried by reading the code. None breaks the design; the ones
marked "needs" are requirements of it.

* **`transactionInfo()`** on a mixed record: breaks as written (point
  4). Needs the copy mark.
* **`appA` at a start:** breaks restart invariance as written (point 4).
  Needs one definition of reclaim's own record.
* **A record that names its own end:** none left but the after-row
  charge (point 1, wart 2).
* **Two decisions in one record that depend on each other:** none (point
  1, "Order").
* **The rerun at a start** (read: `DbStarter`): it gives a record's KVs
  to the tree in stored order, which is the merged batch's order. D is
  rebuilt from the stored got-dirty ids, not from the touch ("the touch
  is not stored, so it is not rerun"). A mixed record reruns as it was
  written.
* **A crash inside the record:** recovery drops or completes the torn
  record (F2's aborted record), both parts together. The user's action
  is then not accepted.
* **A refused user transaction:** its plan is never applied, and the
  stream and memory are unchanged. P2's "a refused request must leave
  the stream unchanged" holds, which Q8 of D2 broke.
* **The cut in the user's own record:** fa moves at this record. The
  user's STM check came before, and readers below the new fa expire as
  today (011-04, W1). The pending cut's durability mark is the end of
  the record, known after the append and not stored.
* **Times:** the copies take the user's time. `transactionInfo()`
  follows a copy back to `tt - 1`, the state before the record, which
  holds the value copied. Times stay strictly increasing (one a record).
* **A value of 8 MiB copied in a commit of 32 MiB:** about 40 MiB in one
  record, far within 2^31 - 9. The write lock is held as long as today.
* **The tests' lowered record limits:** the step is shortened or
  skipped (point 2). A workload made only of transactions at a lowered
  limit gets no step from its commits, only from `maintain()`. This
  happens in tests only; `LimitsTester` mixes sizes, so its commits still
  carry steps (inferred).
* **Index jobs (N9), empty commits, `setStartupDistance`** (a user
  transaction): each carries maintenance like any commit, which is
  harmless.
* **Not tried, not checked:** the cause of G4's M5 at 1.933 (F9); the
  Pub layer under kills; the writer PE with a batch
  that mixes a user's deletes with copies (it takes any batch, so this
  is inferred to work); the proofs of lean/contract beyond the
  statements read.


## 10. The smallest clean design

The rules, each with what, when, by whom, and how it is checked.

1. **One action, one record.**
   * What: every accepted action appends exactly one record. A commit
     appends its transaction's record; a setter, its settings record; a
     `maintain()` part, its part's record. Nothing else appends but
     recovery's completion of a torn record.
   * By whom: `Db`, under the write lock.
   * Checked: a probe at every record boundary (031-05's
     `P2CrashProbe`), with the number of records equal to the number of
     accepted actions and parts.
2. **A commit's record holds its maintenance, decided from the stream
   before it.**
   * When: after the last check that may refuse the user's transaction,
     before the go point.
   * What: `Db.executeLocked` asks `Reclaim.plan` for B or S, then P,
     then C, each as `main` decides it after a commit, with:
     * L0, the stream's length before the record, for the growth and
       for pStart, pEnd and pSafe;
     * the last record's time for tStart, and the last key live then
       for E;
     * the record's time for now and tEnd;
     * sp and mp as the last record left them.
   * Checked: `StreamDigest`, `RestartInvariance`, the probe of rule 1,
     and C-STEP and C-CUT on traces.
3. **The plan's KVs:**
   * the step's copies, the old live KVs that the scan met at the state
     before the record, each with the value it read, with a copy mark;
   * the current row, by a value transformation after the touch of the
     copies' keys;
   * the table, if B, P or C changed it, also by a value transformation
     after the touch, so that its row of the iteration in progress holds
     the step's progress as the current row does (a record may hold S
     with P or with C). The plan changes no memory of reclaim's; it works
     on a copy of the rows.
   * They are merged with the user's KVs after the key transformations,
     one KV a key. A copy of a key that the user writes is dropped. The
     copies are neither STM reads nor STM writes.
   * Checked: a unit test with the user writing a key in the step's
     range, a put and a delete; and C-STEP.
4. **The plan fits the room.**
   * What: the step's value nodes stay within `valueLimit` less the
     user's value bytes. The record carries no step if the user's
     dirty-node count plus the step's bound passes `dirtyLimit`.
   * Checked: unit tests at lowered record limits. 024-17's bound is
     extended by the step's term and proved.
5. **Refusal, failure and stop.**
   * A commit is refused only by its own checks, before the plan. The
     plan reads only.
   * Any exception from the plan on fails the database (P7). A stop
     before the go point refuses the commit, with nothing written.
   * Checked: `before-commit.sh`'s failure tests, and a fault-injection
     test in the plan.
6. **After the record.** `Reclaim.apply` updates reclaim's memory from
   the plan (the rows, fa, fp, the pending cut, the caches dropped at a
   cut) and makes a pending physical cut once the stream is durable.
   Checked: a start's `initFromDb` gives the same memory (the restart
   tests).
7. **Times.**
   * Every record's time comes from `DbClock.transactionBegin`, a
     `maintain()` part's too. There is no hold and no maintenance time.
   * The 1,024 kept times and top ordinals may go.
   * Checked: `HoldProbe` without the hold, with 0 records timed at or
     before a time handed out.
8. **`maintain()`.** Each part is an action with its own time. It
   writes one record, the first that is due of M1 to M6 (031-04, 031-05),
   built through the same path as a commit: an empty action and the
   part's plan. Checked: the probe of rule 1 inside calls, and 031-04's
   count gates.
9. **The setters carry no maintenance**, as on `main`: what a setting
   makes due is decided by the next record that carries maintenance.
   Checked: `ReclaimRetentionTester` (F1).
10. **The copy mark.**
    * What: a flag in a value node's header, set on reclaim's copies
      only (027-03, section 8; a format change).
    * Uses:
      * `transactionInfo()` follows a value back only from a copy, and
        lists the action's KVs without the copies;
      * a record is reclaim's own if each of its KVs is a copy or a key
        of reclaim's (`appA`);
      * the trace marks the copies.
    * Checked: `PubTester`'s `transactionInfo` tests, with a mixed
      record, and C-STEP.
11. **Nothing is due between records.** A call or a start writes only
    its own record. There is no catch-up and no trigger. Checked by
    rule 1's probe.
12. **The after-row charge is not made.** The row charges the copies'
    bytes and its touch's dirty bytes. Checked: the count gates G1 to
    G4, and 031-05's Q3.


## 11. Open questions for Frans, each with a recommendation

* **E1. Take (e), one record, for A1?**
  * Options: (e) as in section 10; (c), the reviewer's variant; (d),
    the compound unit (studied elsewhere).
  * Recommended: **(e)**. It has no state between records, needs no
    start that writes, and leaves the Lean proof to a corollary of
    `T2_restart`. Its cost is about 70 to 130 lines more than (c), the
    copy mark, and changes to the trace and the contract model. If 2026.7's
    date cannot take the larger rework, (c) is the fallback: the bytes of
    both are functions of the stream.
* **E2. The copy mark's form** (a format change).
  * Options: (a) a flag in the value node's header; (b) the record's
    value nodes in two groups, the action's and the copies, with a count
    in the record's header (its three unused bytes); (c) no mark, and
    `transactionInfo()` changed to guess, which is wrong when a user puts
    the same bytes again.
  * Recommended: **(a)**. It is one bit per node, it needs no merge of
    two sorted lists at the rerun, and every reader of a record sees it
    where it reads the node.
* **E3. The after-row charge** (028-26; 031-05, Q3).
  * Options: (a) not made; (b) a deterministic estimate stored in the
    step's row; (c) charge the record's bytes.
  * Recommended: **(a) for 2026.7**, measured with G1 to G4 at node
    sizes 8 and 30, with (b) as a 028 entry. One record makes the exact
    charge harder still, as the batch also holds the user's puts.
* **E4. A `maintain()` part's time.**
  * Options: (a) each part its own clock time, as a transaction's: no
    hold at all; (b) the call's time once, the prototype's, with the
    parts timed from the last record and the hold inside calls.
  * Recommended: **(a)**. A part is an action (F4), and its time is an
    input like a commit's.
* **E5. The 1,024 kept times and top node ordinals** (015-55, 005-02).
  * Options: (a) remove; (b) keep as a margin.
  * Recommended: **(a)**, as its own small change after the landing.
    Nothing writes after a commit any more, and parts and setters are
    refused at the bound as commits are.


## 12. State

2026-11-27, 11:15 at the latest.

* **Done:**
  * the nine points;
  * the design (section 10) and the questions (section 11);
  * the probe `probes-a1/OneRecordProbe.java`, with its six runs in
    `probes-a1/one-record-runs.txt`, committed on the clone's branch
    `a1-one`.
* **Not done:**
  * no prototype of (e);
  * no `before-commit.sh` run;
  * no measurement of P1;
  * lean/contract's proofs not read in full;
  * 024-17's bound with the step's term not derived.
