# 024-16, review (rev16)

An independent review of the branch `024-16-one-operation-a-key`, head
`d5617d45` (`023bfa22` the change, `d5617d45` the six expected values),
on `main`'s `68c3917e`, before it lands. By rev16, an agent of coord-1111,
2026-11-11, 11:57 to 12:20. I read the diff first, then the item (024-16).

Where: my clone `/Users/f/fl/bench/2026-11-11/rev16/clone` at `d5617d45`
(clean, nothing changed), the base as a worktree
`/Users/f/fl/bench/2026-11-11/rev16/base` at `68c3917e`, the probes in
`/Users/f/fl/bench/2026-11-11/rev16/probe/` (`bergdb/core/Probe16.java`:
p1, p2, p3; `bergdb/pubimp/ProbePub16.java`). Findings are R1 to R4 (this
branch), B1 (beside it), questions Q1 to Q3.


## 1. Verdict

**LAND WITH FIXES.** I found no fault in the commit path: not by
reading, not with a concurrency probe that has teeth (section 3). The
fixes are small, and none of them is in the logic of the commit:

* **R1**: give a refused `Trans` its `tt` back, as its keys and hashes
  (or say in `Trans.tt`'s Javadoc that it means nothing after a refusal).
* **R2**: `DbClock.transactionBegin`'s Javadoc is false after a cancel.
* **R3**: `docs/levels.md` lists the refusals before the go point and
  what fails the database; it names neither the new refusal nor a key
  transformation that throws before the go point. AGENTS.md says that
  levels.md is kept up to date with the code.
* **R4** (nit): the loop that looks for equal neighbours is outside the
  `catch (Error)` of `transformKeys`.

Landing without them writes no wrong data. If the coordinator lands now,
R1, R2 and R4 can follow. R3 should land with the branch or right after.


## 2. Findings, by severity

### R1 (low; shown by a run). A refused Trans keeps `t.tt`

* **Where:** `Db.executeInner` sets `t.tt = dbClock.transactionBegin(...)`
  (Db.java line 2508). `transformKeys` (line 3007) puts the keys and the
  write hashes back on a refusal, but not `t.tt`.
* **Scenario:** probe p1 refuses a `Trans` with the clock at 3000. After
  the `DbException`, `t.tt` is 3000. The next transaction commits at 3000
  too, by design (`transactionCancel`). By reading `transactionBegin`:
  if the clock has gone back and no `currentTime()` came in between, the
  next transaction commits at a time earlier than the refused `t.tt`.
* **What goes wrong:** `Trans.tt`'s Javadoc says "The transaction's
  time, set by Db.execute(): ... later than every transaction's before
  it; a read at it or later sees the transaction". That is false for a
  refused `Trans`. It also breaks the brief's and the item's (S5) "a
  refused run leaves the Trans as it was before the call". A reused
  `Trans` that committed at T0 and is then refused shows T, a time that
  no transaction has, or that another transaction has.
* **New with 024-16:** no earlier refusal set `t.tt`.
  `transactionBegin` was the last step before the go point, and it
  throws before the assignment.
* **Fix:** keep `t.tt` before the assignment in `executeInner` and put
  it back in the refusal branch of `transformKeys` (pass it in, or put
  it back in `executeInner` around the call). Or document it.
  `testRefusedTransUnchanged` could check `t.tt` with the other fields.

### R2 (low; by reading, and by the change's own test). `DbClock.transactionBegin`'s Javadoc

DbClock.java line 150: "The returned time is guaranteed to be strictly
larger than any previous read time and any previous transaction time
returned by this object." After `transactionCancel()` the next call
returns the same time: `testTransactionCancel` asserts `2*F` twice. Fix:
"... than any previous transaction time of a transaction that ended
(transactionEnd)", and that a cancelled transaction's time may be given
again.

### R3 (low; by reading). `docs/levels.md` not brought up to date

* **Where:** levels.md lines 129 to 141 ("`Db.executeInner` has a go
  point. Before it, everything that may refuse the transaction is
  checked ..."). The list names the STM check, the top node ordinals,
  the size, the dirty index nodes and the clock. It does not name the
  new refusal.
* **Also:** lines 103 to 107 and 121 to 123. The failures listed there
  are an Error, the storage, and "any exception after a transaction's go
  point". Then: "Everything else ... fails only that call, and the
  database goes on: a transaction refused before its go point". A key
  transformation that throws a `RuntimeException` now runs before the go
  point, yet it still fails the database. Probe p3: `DbFailedException`
  "The transaction at time 3 failed after it began ...", and every later
  read is refused. levels.md does not say so.
* **The item** (section 7) says "docs/levels.md does not state the rule;
  not changed". But levels.md lists the refusals, so it is out of date.
* **Fix:** add the refusal to the list ("two keys as written that its
  key transformations make one key, 024-16"). Add a sentence that a key
  transformation's exception fails the database although it runs before
  the go point (its Javadoc: it must not throw). Or make that exception
  a refusal (Q1).

### R4 (nit; by reading). The neighbour loop is outside the `catch (Error)`

* **Where:** Db.java line 3032. The `Keys.compareArrays` of
  `transformKeys`'s neighbour loop is outside both of its `try` blocks.
* **What could go wrong:** take an `Error` there (a
  `StackOverflowError`; `compareArrays` allocates nothing). It leaves
  the `synchronized (writeLock)` block with the clock still running.
  `execute()`'s `catch (Error)` records it only after the lock is
  released. That is against 019-40, and against the method's own comment
  ("under the lock, as above"). A writer waiting for the lock could then
  run `transactionBegin` on a running clock (an `AssertionError` with
  `-ea`).
* **Practically unreachable:** `transform()` ran deeper on the same
  stack just before.
* **Fix:** wrap the loop in the `try`/`catch (Error)` that the refusal
  branch has. Or find the first equal pair inside the first `try` and
  refuse after it.

### B1 (beside the change; old; shown by runs on the base and the branch). A stale index entry across two transactions

* **Where:** `RwEnvironmentImp.indexEntries`, line 500. A put whose key
  is replaced is taken to have no previous value ("lands at a key ...
  which no key replace wrote before").
* **Scenario:** probe `ProbePub16` runs these steps:
  1. A TestClock.
  2. `/o/` with an index on `v`.
  3. An earlier transaction puts `Kt` (the digits of the next-but-one
     time) with `v` = 5.
  4. A transaction of its own holds `put("/o/${transactionTime}", v = 7)`
     alone. It commits at that time.
* **The result:** `Kt` holds 7, and the index scan gives "Kt 7" alone.
  **Two entries are stored**, one of them `Kt`'s old `v` = 5, which
  nothing takes back. It is the same on `68c3917e` and on `d5617d45`.
* **Not this branch's fault:** there is no collision inside one
  transaction, so 024-16's rule does not reach it, and the item does not
  claim it. But "no stale entry can be stored" (the new Pub test's
  Javadoc) holds only for collisions inside one transaction. 024-10's
  F1 is closed for that case only.
* **Impact:** it needs a guessed future time (a TestClock, a clock that
  stands still). No scan's answer is wrong (020-10, section 3.4). For
  024-10's F1 or a follow-up, not for this branch.

### Questions (not faults)

* **Q1. A key transformation that throws.** It now runs before the go
  point, and the restore and `transactionCancel` are at hand. So it
  could be refused (keys and time back, a `DbException` with the cause)
  instead of failing the database. The branch keeps the failure
  (`KeyTransformation`: "must not throw"). Either is defensible. If the
  failure stays, R3's sentence is needed.
* **Q2. The refused transaction's time is shown, then given again.** The
  message shows it (the Pub key with the digits), and the next
  transaction takes it (by design; tested). A user who reads at that time
  sees the answer change when the next transaction commits. But that
  time was never handed out as a read time: `currentTime()` gave at most
  T - 1. So no promise is broken. A clause in the message or the Javadoc
  could say so.
* **Q3. The size checks could count the final keys.** The
  transformations now run before the go point. So `checkSize` and
  `checkDirtyNodes` could count the final keys, refusing with
  `transactionCancel` (015-51: "the new key is not size-checked"; the
  cheap count uses the key's length as written). A follow-up, not this
  branch.


## 3. What I checked and found sound

**1. The commit path under concurrency.**

* **Every caller of `DbClock`, by grep:**
  * `currentTime`: `Db.currentTime`, used by users, the Pub layer's
    `DatabaseImp` and `ConnectionImp`, and `Jmx`.
  * `lookupTime`: gets, `getMany`, `warmup`, `checkDirtyNodes`, the Pub
    layer's `fixReadTime`.
  * `transactionBegin` and `transactionEnd`: `executeInner`,
    `writePrimordialTransaction`.
  * `setLastTransTime`: the startup.
  * `transactionCancel`: `transformKeys` only.

  Only `currentTime` reads `transactionRunning` and `transactionTime`.
  `lookupTime` reads only `lastTransactionTime`, which a cancel leaves
  as it is.
* **By reading (an argument, not a proof):**
  * `currentTime()` hands out a time at most `lastReadTime` after the
    call. Both branches now keep it.
  * `transactionBegin` takes a time later than `lastReadTime` and
    `lastTransactionTime`, and a cancel lowers neither.
  * So a committed time is later than every time handed out before its
    begin. A time handed out while it runs is T - 1 < T. After
    `transactionEnd` the time is T or later, and the changes are
    published (`readSync`) before `transactionEnd`.
  * So a read at a time handed out cannot change.
  * The new line in `currentTime` changes nothing for a transaction that
    commits (T > T - 1).
* **By a run, probe p2:**
  * Set-up: 2 or 3 reader threads call `currentTime()` and read a key at
    the time it gave. One writer alternates refused and committed
    transactions.
  * Clocks: one that stands still, one in 1 ms steps, and one that goes
    back at random. 8 to 10 s each.
  * Size: per run, 1.4M to 2.8M refusals, as many commits, 8M to 12M
    reads.
  * Result: 0 mismatches with the committed history, 0 changes on a
    re-read, and `currentTime()` never went back in a thread.
  * The probe has teeth. With mutation MA (the new `lastReadTime` line in
    `currentTime` dropped), p2 on the clock that goes back found 4,519
    mismatches and `currentTime()` going back, p1 said FAULT, and
    `DbClock.testTransactionCancel` failed ("Expected 29999, got
    20000").
  * So I found no fault; I have not shown that there is none.
* **Probe p1:** the refused transaction's key transformation calls
  `currentTime()` and reads at that time, while the clock goes back
  during the transaction. It got r = 2999. The next transaction's time
  was 3000, and the read at r gave the same value afterwards.
* **The STM:** `stmCheckConflicts` runs before `transactionBegin`, and
  `stmRecordKeys` after `transactionEnd` with the final hashes, as
  before. A refused transaction records nothing. Take a read time T - 1
  from `currentTime()` during a refused transaction. It is checked
  against a later commit at T or later: `modifiedAfter(T - 1)` finds it.
* **The Pub layer's retry:** `executeRwInner` catches only
  `RerunException`, so a `DbException` leaves at once (tested: the
  action runs once).
* **Work after the go point:** reclaim, eviction, the dead hand, the
  listeners (`transExecuted`, `transactionCompleted`) and the audit all
  run after the go point, so a refusal never reaches them. Internal
  transactions have no key transformation, so `transformKeys` returns
  `t.kvs` for them.
* **Locks:** a user's transformation ran under `writeLock` before too
  (`putKvs`). It is not under `DbClock`'s monitor. `transactionCancel`
  takes that monitor under `writeLock`, the order of `transactionBegin`
  and `transactionEnd`. Nothing moved out of the lock. `close` and
  `stop` wait on `writeLock`, not on the clock.
* **Every way out of the new code:**
  * A refusal: keys and hashes put back, the time given back, a
    `DbException`; the database stays active.
  * A transformation that throws a `RuntimeException`: `fail()`, a
    `DbFailedException`, the database failed, and the clock left running
    as before 024-16 (p3).
  * An `Error` in a transformation or in the sort: `fail()` under the
    lock.
  * An `Error` while the message is built: `failed()` under the lock.
  * The exception is R4.
  * No call in the new code can be interrupted.

**2. The restore.**

* The keys and hashes of every transformed KV are put back at any
  collision, not only the pair's: the loop runs over all of them.
* The `kvs` array is the same, with the same `Kv` objects in the same
  order (`sortByKey` sorts a copy). Virtual write hashes, beyond
  `kvs.length`, are not touched.
* A reused `Trans` that is refused, committed, then refused again
  (U1, U2) is covered.
* So are two `Trans` of one builder that share `Kv` objects
  (`testTransformedKeysSorted`).
* All of this except `t.tt` (R1).
* An assumption: a transformation replaces the key with `setKey`. Every
  one does (the Pub layer's, the tests'). One that changed the array in
  place would not be put back. `KeyTransformation`'s "allowed to modify
  trans.kvs[index].key" can be read to allow that; a nit: "set a new
  array".

**3. The detection.**

* All KVs are sorted with `compareArrays`, the comparator of `build()`'s
  `TreeMap`. It is 0 only for equal arrays, and so is `compareKeys`. So
  equal final keys are neighbours, whatever the order of the calls.
* Three keys into one: the first pair is found.
* A transformed key equal to an untransformed one: found (T1, T2, T7,
  T8).
* After the Pub layer's replace: found (P4 to P8, the new Pub test).
* The empty key: the builder refuses it as written. Two empty keys made
  by transformations would be refused. One reaches `putKvs`, as before.
* Not refused: a KV and itself (only distinct places are compared), and
  prefixes or 7-byte segment boundaries (arrays of another length or
  content compare unequal).
* The message names the keys as written and the final key, each cut at
  100 characters.

**4. What moved.**

* `checkSize`, `warmup` and `checkDirtyNodes` still count the keys as
  written, as before.
* The touch of a reclaim step now comes after the transformations. It is
  internal only, with no transformation.
* `stmRecordKeys` records the final hashes, as before.
* No dedup: the record holds every KV, as `checkSize` counted them.
* StreamDigest: identical (the item).

**5. The tests.**

* The new tests fail on the old code, by reading: they expect refusals,
  and the `DbClock` test needs the new method.
* **My mutations.** Each was built and run against `DbClock`,
  `DbTester`, `DbTesterDelete` and `PubTester`. Baseline: 246 tests
  pass.
  * **MA** (above): caught by `DbClock.testTransactionCancel`.
  * **MB**, the keys put back but not the write hashes: caught only by
    `testRefusedTransUnchanged`'s array check. Putting the hashes back
    has no other effect that the suite sees, as every transformation
    sets its hash again.
  * **MC**, collisions looked for only between neighbours of `t.kvs` in
    call order, not in the sorted copy: caught by
    `testTransformedKeysSorted`, `testOneOperationAKeyAfterTransformations`
    and `testRefusedTransUnchanged`. The T rows, U1 and U2 and both Pub
    tests pass under MC: their two keys are neighbours as written.

**6. Smaller things.**

* `git diff -w` differs from the diff in 5 lines, all inside the change.
  Nothing unrelated is in it.
* `RwEnvironmentImp`'s maps are `HashMap`s again. Their order is read
  only by `createTrans` (the builder sorts) and `indexEntries` (each
  object's entries alone).
* The Javadoc of `Db.execute`, `Trans`, `KeyTransformation`, `Connection`
  and `WBuilder` matches the behaviour, but for R1 and R2.
* Wording nits:
  * `transformKeys`' Javadoc says "is refused: one operation a key
    reaches the index, with no exception". That reads as if no exception
    is thrown; it means "without an exception to the rule".
  * The comment rewrap in `Dag.java` leaves "Nothing is changed" and
    "yet." on two lines.


## 4. What I did not check

* No gates (before-commit.sh, the level scripts): the item's and the
  coordinator's.
* The C clone and the Lean model (024-16, sections 11 and 12): read only.
* p2 is short runs on one machine (F53). Other hardware and other JIT
  interleavings are not covered.
* The stopping path: a refusal, or a transformation that throws, while
  `stop()` runs. Read only: `fail()` hands the exception back as it is
  while stopping, as before.
* Pub workloads with collisions under concurrency, such as an `rw()`
  with conflicts and then a refusal: not run.
* The cost of `transformKeys` is not measured. By reading: two arrays of
  n and O(n) more work, only for a transaction with a key
  transformation.


## 5. State

Done, 12:20. Nothing changed in the strict clone or in the main tree but
this file. My clone is clean at `d5617d45`. The probes and the base
worktree are under `/Users/f/fl/bench/2026-11-11/rev16/`.
