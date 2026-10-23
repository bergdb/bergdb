005-01. Fix M49: a transaction that throws is half committed
============================================================

Status: done (2026-10-22; see Outcome). Kind: fix. Created 2026-10-19.


The issue
---------

A transaction that throws inside `Db.putKvs` is half committed. Its time
becomes readable with some of its changes in memory; the nodes it made stay
in the cache and in the writer's node list, and the next transaction writes
them as its own. Register row M49 of
[docs/level4-alignment.md](../../docs/level4-alignment.md). The full
analysis, with a reproduction, the causes in the code, the fix options and a
test plan: [item 003, 003-01](../003-transaction-exception-safety/01-finding.md).

What can trigger it: a value or key transformation that throws, an `Error`
(out of memory, an assertion), the ordinal bound (M46, 005-02), and a read
error when a put loads a node. Since Level 4 (eviction on by default) the
writer loads evicted index nodes during puts, so an I/O error in the middle
of a transaction is now an ordinary failure path, not only a lazy-startup
one. Frans decided on 2026-10-17 that it blocks nothing and is fixed later;
this is the later.

2026-10-21: a transaction too large for its record was a trigger too; 005-17
refuses it before the go point.


Frans
-------

Note the pre-2026 work on this. This is a central design of the database.
No roll-back of in-memory state. Instead, conditions are tested first and when a transaction
get the go signal it will always run without any exceptions thrown
as long as the required environment for the data is working; that is: 
storage, JVM, memory. And if any of those fails, the database cannot function. 
It should be restarted.



The task
--------

Fix it as 003-01 recommends, unless the work shows a reason not to:

1. **Fail-stop** (003-01, 5.1): any `Throwable` from `putKvs` or from
   `store()` marks the database failed; every later transaction is refused
   with a clear exception until a restart, which rebuilds the state from the
   stream (the restart argument, T2 and T8, already proved). Decide whether
   reads are refused too (safer) or allowed with a documented caveat.
2. **Transformations first** (003-01, 5.2): compute value and key
   transformations before the first change, so bad input to a counter does
   not stop the database. Check first whether a transformation today sees the
   earlier puts of its own transaction; the semantics must not change.
3. Clear (or assert empty) `x.transNodes` at `x.begin`.

Decide in the work: does the Lean model need to say anything? The model's
runs have no failing transactions; a fail-stop leaves the stream as the
model's run without the failed transaction, so probably no model change, but
say so explicitly in `level4-alignment.md` (row M49).


Done when
---------

* 003-01's test plan passes: the reproduction as a unit test; a put that
  fails on a read error, also with an evicted node; an exception in
  `store()`; no `two canonical objects` with assertions on.
* No stream changes when nothing throws: StreamDigest identical to R8's.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.
* M49 is closed in the register, item 003 is closed, `docs/` says what a
  failed transaction does (the public API's documentation included).


First step
----------

Reread 003-01 against today's `Db.executeInner` (item 001 changed it a lot
after 003-01 was written at `059dbf1`) and update its section 3 and 5 where
the code moved.


Size and order
--------------

S to M: the fix is small; the tests with failing reads and appends are most
of it. Do it together with 005-02, which changes `Db.executeInner` too, as
one change with one run of `before-commit.sh`, or as two commits in a row.


Outcome
-------

2026-10-22, by Claude (Opus 5.5, Claude Code), as Frans decided ("Do as
proposed / Recommanded. Implement this and commit it. Refuse both reads and
writes after failure. Use the wrapper as recommanded. Task 2, as you
recommend."): 003-01's 5.1 with reads refused too, and not 5.2. It is
Frans's design above, made explicit in the code: the checks come before a
go point, and nothing changes before it; after it, a `Throwable` means that
the storage, the JVM or memory failed, or a bug, and the database fails. No
rollback.

**The first step.** 003-01 reread against `Db.executeInner` at `cbeb9bd`;
its sections 3 to 5 have notes of the day. The causes were all still there.
Since 003-01, 005-02, 005-17, 005-18 and 005-21 had moved every check that
depends on input before the first change, and the Pub API runs the
application's code (the action, the index functions, the conversion of
objects) before `Db.execute`. What could still throw after the go point: a
load in a put or in a reclaim step's touch (an I/O error, a corrupt node),
the append in `store()`, an `Error`, a bug, and reclaim's work after the
transaction (its internal transactions and the cut). The design before 2026,
in the f1 repository's F1-007 (`a/007-bergdb-261012/bergdb/doc/`):
2008-08-02, "Support for rollback? Answer: No. If transactions are
deterministic, we don't need this, we can always check input data before we
start to modify data" (`log-old/2008-2011-log.txt`); 2012-08,
`FatalDBException`, "an error happened in the database that makes it
unusable. Usually handled by logging the error and stopping the database"
(`2012/2012-08-layers.txt`); 2013-01, "We do not want the application to
run if its environment (needed assumptions) is faulty or if there is a bug"
(`2013/2013-01-notes.txt`, Warnings).

**The change**, in `java/src/bergdb/`:

* `core/Db.java`, `executeInner`: the go point is after
  `dbClock.transactionBegin()`. Everything after it, from `putKvs()` to
  reclaim's listener, is in one `try`, whose `catch (Throwable)` calls
  `fail()`. `dbClock.transactionEnd()` follows `putKvs()` in the `try`, no
  longer in a `finally`: when the puts throw, the transaction's time never
  becomes a lookup time, and a read that comes in before the database is
  seen as failed reads the state before the transaction, by the property
  that lets readers run beside the writer. The state is checked again under
  the write lock: `execute()` checks it before it waits for the lock, so a
  writer that waited while another failed would otherwise run on the
  leftovers and write them.
* `Db.fail()`: keeps the first failure, sets `DbState.FAILED` and publishes
  it with `readSync`, as `stop()` does; returns a `DbFailedException` with
  the cause, and throws an `Error` as it is. A `DbFailedException` from a
  reclaim transaction inside the listener passes as it is. While the
  database is stopping, the exception is thrown as before: `stop()` closes
  the storage without the write lock, so a running transaction's append can
  fail.
* `Db.assertDbStateIsActive`: in `FAILED`, a `DbFailedException` with the
  first failure as the cause, so `execute`, `getOne` and `getMany` refuse,
  and with them the Pub API. `sync()`, `stop()` and `close()` do not check
  the state.
* `Db.ExecuteData.begin` asserts that `x.transNodes` is empty. `putKvs`
  still clears its marks (its comment said "in case an earlier transaction
  ended with an exception"), as the puts of startup (`DbStarter`) use the
  same listeners.
* `core/DbState.java`: `FAILED`, ACTIVE -> FAILED -> STOPPING.
* `pub/util/DbFailedException.java`, new: `extends IllegalDbStateException`;
  in the Pub API's package, as its documentation names it.
* `core/ValueTransformation.java`, `core/KeyTransformation.java`: a
  transformation must not throw (KeyTransformation said so already); it
  runs after the go point.
* `pubimp/IndexBuilderImp.java`, `pubimp/DatabaseImp.java`: the background
  threads that create and delete indexes end quietly on a
  `DbFailedException`, as on a `DbStoppingException`, and go on after the
  restart.
* Javadoc: `Db.execute`, `pub/Database` (the rule for applications),
  `Connection` (`put`, `delete`, `rw`, `get`, `exists`), `WBuilder.execute`,
  `IllegalDbStateException`, `DbState`.

**Task 2, not done**, as Frans decided. The check it asked for: a
transformation does not see the earlier puts of its own transaction, since
its previous value is read at a lookup time before the transaction
(`DbClock.lookupTime` caps it at the last transaction's time); a pure
transformation could move before the first change and give the same value.
But reclaim's (`Reclaim.step`, the table row) reads `Trans.dirtiedBytes`,
which the touch and the step's earlier puts produce: moved, it would store
another row, change the stream and miscount Level 3's allowance. And no
transformation that the Pub API reaches can throw on input:
`ValueTransformation` is used by reclaim and by tests only, and the Pub
API's one `KeyTransformation` is the `${transactionTime}` key, a time of 18
digits, in range since 005-18.

**Tests**, in `core/DbTesterFailure` (new; six unit tests, about 0.25 s
together, and an f-test):

* `testValueTransformationThrows`: 003-01's reproduction (2.1). The call
  gets a `DbFailedException` with the transformation's exception as the
  cause; the lookup time stays that of the transaction before; a later
  transaction, a `getOne` and a `getMany` are refused, with the same cause;
  `sync()` works; nothing more is appended; a restart, with the audit on,
  gives /a = a0 and /b = b0, and takes a transaction.
* `testErrorIsThrownAsItIs`: an `Error` in the transaction is thrown as it
  is, and later calls get it as the cause.
* `testReadErrorInPut`: a read error (an `IOException` from the test stream
  `FaultStream`) when a put loads an index node that eviction released:
  node size 8, a startup distance of 1,000 bytes, every evictable object
  evicted after every transaction, 2,000 keys. The put's path is not the
  warm-up's: a key transformation gives its key, as the `${transactionTime}`
  key does, and makes the stream fail, after the transaction's first put has
  changed the Dag. The same checks; a restart, with the audit on, gives
  every key's value and nothing of the failed transaction.
* `testCorruptNodeInPut`: the same with a corrupt node (a checksum error),
  where the storage stays healthy; nothing more is appended either. On the
  code before the fix this is the case in which the next transaction
  committed with the failed one's nodes (the probe, below).
* `testAppendErrorInStore`, an f-test (0.5 s: a sync waits for
  StorageManager's 500 ms poll): appends fail; the next transaction is in
  memory and buffered, the sync fails, and the transaction after fails in
  `store()`, with the `StreamIoException` as the cause; a restart gives the
  state before both.
* `testWriterWaitingForTheLock`: a second writer waits for the write lock
  (seen with `ThreadMXBean`) while the first transaction's transformation
  throws; it is refused when it gets the lock, and a restart has neither.
* `testRefusedBeforeTheGoPoint`: a transaction refused before its go point
  (a `RerunException`) changes nothing, and the database goes on.
* `DbTesterStream.testReadOnlyStream2`, changed: its third transaction's
  append fails in `store()`, so it expects a `DbFailedException` with the
  `StreamIoException` as the cause (it was the `StreamIoException`), and
  the next transaction refused.

Each part of the fix has a test that fails without it
([mutations.txt](01-fix-m49-exception-safety/mutations.txt), made with
[mutations.sh](01-fix-m49-exception-safety/mutations.sh) and
[mutate.py](01-fix-m49-exception-safety/mutate.py)): without the fix (the
`finally` of before, no fail-stop), five of the six unit tests and both
f-tests fail; with the fail-stop but `transactionEnd()` in a `finally`, the
three checks of the lookup time fail; without the state check under the
lock, the waiting writer runs and stops at the new assertion in `x.begin`
("the nodes of another transaction").

**The Lean model.** No change. Its runs have committed transactions only.
After a failure the stream holds whole records (a transaction is appended in
one call, `NodeStream.appendNodes`), and nothing is appended after it, so it
is the stream of a model run without the failed transaction, or with it if
its record was appended before the failure; an append that fails part way
is a torn record at the end, recovery's case (T1). A restart from it is
covered by T1, T2 and, after cuts, T8. Written in docs/level4-alignment.md
(row M49, 6.4 and 8) and docs/levels.md ("A transaction that fails").

**Evidence.**

* The probe ([M49Probe.java](01-fix-m49-exception-safety/M49Probe.java),
  [probe.sh](01-fix-m49-exception-safety/probe.sh)), 003-01's case and a
  corrupt index node, on the code before the fix
  ([probe-before.txt](01-fix-m49-exception-safety/probe-before.txt)) and
  with it ([probe-after.txt](01-fix-m49-exception-safety/probe-after.txt)).
  Before: /a = a1 was readable after the failure and the next transaction
  committed; after a restart, /a = a1 in the first case. In the second, the
  next transaction committed with the failed one's nodes in its record
  (2,696 bytes), and after a restart neither /a nor that transaction's own
  /c could be read, although the restart had its time: a committed and
  synced transaction lost. With the fix: refused, nothing appended, and the
  restart gives the state before.
* StreamDigest `all` against the build before the change: `DIGESTS IDENTICAL
  (36 of 36)`, and against R8's digests too
  ([digest-compare.txt](01-fix-m49-exception-safety/digest-compare.txt)). No
  record changes.
* `before-commit.sh`: BEFORE COMMIT OK (974 unit tests, 63 f-tests).
* The four gates, full, one after the other, in the scratch clone
  ([gates.txt](01-fix-m49-exception-safety/gates.txt)): `LEVEL 1 OK` (130 s;
  Props: MEM 192, SS 1.50, within their limits), `LEVEL 2 OK` (731 s;
  conformance 70 of 70 traces `TRACECHECK OK`), `LEVEL 3 OK` (497 s; 25 of
  25 traces with cuts, `POWERLOSS OK`), `LEVEL 4 OK` (871 s; 33 of 33
  traces, C-P on 7,917 transactions; 640,953 audits in its runs, none
  failed). Unit tests: 974 of 974 in each, six of them new. No timing was
  measured: on the path of a transaction that does not throw, the change
  adds one read of the state under the lock.

**Done when**, point by point:

* 003-01's test plan: the reproduction (`testValueTransformationThrows`); a
  put that fails on a read error, also with an evicted node
  (`testReadErrorInPut`, `testCorruptNodeInPut`); an exception in `store()`
  (`testAppendErrorInStore`, `testReadOnlyStream2`); no `two canonical
  objects` with assertions on (the audit at the tests' restarts, the new
  assertion in `x.begin`, and the gates' audits).
* No stream changes when nothing throws: StreamDigest, above.
* `before-commit.sh` prints `BEFORE COMMIT OK`: above.
* M49 closed in docs/level4-alignment.md, item 003 closed; docs/levels.md
  says what a failed transaction does ("A transaction that fails", and the
  fourth of the bugs found by the alignment of Levels 3 and 4), and so does
  the public API's documentation (`Database`, `Connection`, `WBuilder`,
  `DbFailedException`). Also docs/log.md.

**Follow-up, 2026-10-23**, at Frans's request: `DbException`'s Javadoc
called every `DbException` fatal, so that the database should not be used
after one; a refusal before the go point leaves it as it was. It now names
the two kinds, refusals and failures, and says that taking any
`DbException` as a reason to restart is always safe.
