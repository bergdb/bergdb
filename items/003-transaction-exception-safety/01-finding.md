003-01. A transaction that throws in the middle is half committed
=================================================================

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-17. Found in
item 002 while probing the top node ordinal bound
([02-report.md](../002-top-node-ordinal-bound/02-report.md), sections 2.3
and 8). Register row M49 of
[docs/level4-alignment.md](../../docs/level4-alignment.md). Line numbers are
at `a3b4421`. No code was changed.


## 1. The finding

When an exception is thrown inside `Db.putKvs`, after the first put of the
transaction has changed something, `execute` throws, but the transaction is
not undone:

1. Its time becomes readable, and readers see the changes made so far.
2. The next transaction that commits writes the failed one's nodes in its own
   record, its value nodes included, so the failed puts become durable.
3. The next transaction reuses the node ids of the failed one's new nodes.

So a transaction that the application sees fail is partly committed. This
breaks atomicity (Level 2), and in the worst case seen it made the database
impossible to start (2.2).


## 2. Reproductions

Both probes are in item 002's [02-report/](../002-top-node-ordinal-bound/02-report/),
with their outputs in its `outputs.txt`.

### 2.1 A value transformation that throws (no bound)

`M46Throw`, today's code (`059dbf1`), in-memory database. Transaction 1
puts `/a = a1`, then `/b` with a `ValueTransformation` that throws.
Transaction 2 puts `/c = c2`. Then a restart from the stream. With and
without assertions:

```
transaction 1 threw: java.lang.IllegalStateException: the transformation fails
after transaction 1: /a = a1, /b = b0; nodes left in the transaction's node list: 1
transaction 2 (put /c = c2) committed; its record holds the values: a1 c2
before the restart: /a = a1, /b = b0, /c = c2
after the restart: /a = a1, /b = b0, /c = c2
```

`/a = a1` is visible right after the failure, and transaction 2 makes it
durable.

### 2.2 The top node ordinal bound

`M46Bound` (item 002, 2.3), with a scratch hook that starts the ordinals near
2^30 − 1:

* `/a` and `/b` in one transaction, where `/a` fits in the root and `/b`
  splits it: the transaction throws, a reader sees `/a = A130`, never stored;
  after a restart, `/a = A117`. Here the failed value was visible but not
  durable, because no transaction committed before the restart.
* 1,000 keys: the transaction after the failure stores the failed one's value
  with its own (its record holds `v1443 v1444`), and from then on the stream
  cannot be started: the startup's rerun replays the failed put, which fails
  again. With assertions on, every later transaction that makes a node fails
  with `AssertionError: two canonical objects for node N` (the reused ids).


## 3. The causes

`Db.executeInner` (1377):

```
synchronized (writeLock) {
    x.begin(t);                       // a new TransInfo; x.transNodes is not cleared
    stmCheckConflicts(t);             // may throw RerunException: before any change, fine
    try {
        t.tt = dbClock.transactionBegin();
        putKvs();                     // 1395: changes the Dag in memory, put by put
        ...
    } finally {
        dbClock.transactionEnd();     // 1409: runs also after an exception
    }
    stmRecordKeys(t);
    store();                          // 1414: writes x.transNodes, adds x.transInfo to TransSeq
    ...
    x.end();                          // 1426: clears x.transNodes
}
```

An exception from `putKvs` skips everything after the `finally`:

* `dbClock.transactionEnd()` makes `t.tt` the last transaction time, so
  readers use it as a lookup time.
* Puts that finished before the exception appended their klongs at `t.tt` in
  place, to nodes that existed before (`Dag.setValue`, `appendKlongs`). They
  stay. (When a later put of the same transaction replaces such a node,
  `Dag.handleFullNode` would take the klongs out again with
  `toPreviousState`, but it runs after the split, which is what threw in the
  bound's case.)
* New nodes were reported to the node change listener: they are registered as
  canonical in `Cache3` and added to `x.transNodes`. `x.end()` does not run,
  so `x.transNodes` keeps them, and the next transaction's `store()` writes
  them in its record. Their ids come from `x.nextVpos`, which `x.begin`
  resets from the stream's next position; nothing was written, so the next
  transaction hands out the same ids again.
* From reading the code, not tested: nodes that the failed transaction made
  dirty (`endOfOp`, `makeDirtyIfNeeded`) are flagged dirty but listed only in
  its `TransInfo`, which never reaches `TransSeq`. So `TransSeq.take` never
  writes them, while their flag keeps a later transaction from listing them.

The same class of problem, not tested: an exception in `store()` (for
example a `StreamIoException` from `nodeStream.appendNodes`, 1465) comes
after `dbClock.transactionEnd()`, so the transaction's changes are visible
while its record may be missing or incomplete, and `x.end()` is skipped.


## 4. What can trigger it

Today:

* A value or key transformation that throws (`Trans.Builder.put` with
  transformations; `ValueTransformation` is meant for counters). Reclaim uses
  one for its current row.
* A read error when a put loads a node from the stream (lazy startup since
  item 001's stage 1).
* An `Error`: out of memory, an assertion.
* The top node ordinal bound (M46), not reachable today (item 002, 2.1).

In normal operation none of these happen, which is why no test has met it.

With Level 4 (item 001, stage 4): evicted index nodes are loaded again by the
writer during puts, so a read error in the middle of a transaction becomes a
normal failure path. Item 001's register (M49) puts the fix before J3.


## 5. Fix options

### 5.1 Stop the writer (fail-stop)

Catch any `Throwable` from `putKvs` and from `store()` in `executeInner`, mark
the database failed (a new `DbState`, or a flag), and refuse every later
transaction with a clear exception until the database is restarted. Reads may
go on, or be refused too: after a failure in `putKvs` they can see the
partial changes, so refusing them is safer (5.3).

Why it is enough: the stream holds only committed records, as long as no
later transaction writes the leftovers, and a restart rebuilds the state from
the stream (Levels 1 and 2). It needs no undo logic, and its correctness
argument is the restart argument the project already has (T2, T8).

Cost: a few lines in `Db.executeInner` and `Db.execute`, the state, and
tests. An exception becomes an outage until the application restarts the
database, which is the right behavior for an I/O error or an `Error`, but
harsh for a transformation that throws on bad input.

### 5.2 Finish what can fail before the first change

Compute every value and key transformation before the first put (they read
the database at the transaction's time, which no put of the same transaction
can change if they run first), and load every node the puts will need before
the first change (a warm-up under the write lock). Then `putKvs` only changes
memory and cannot fail except with an `Error`.

Cost: what a transformation sees must stay the same. Today it reads with
`getOne(x.trans.tt, ...)` at the transaction's own time, after the earlier
puts of the same transaction, so whether it sees them must be checked before
moving it; the warm-up must follow the same paths as the puts, splits
included, which is hard to guarantee under eviction. So 5.2 can remove the
common causes (transformations) but not all of them.

### 5.3 Undo

Make a failed transaction leave no trace: roll back the klongs appended at
`t.tt`, unregister its new nodes, clear its dirty marks and node list, and
take back `dbClock.transactionEnd()`. Readers must not have seen `t.tt`
meanwhile, so `transactionEnd` must move after the point where nothing can
fail. This is the most work and touches the Dag's invariants; the Lean model
would need to say what a failed transaction leaves.

### 5.4 Recommendation

5.1 first, for every exception from `putKvs` and `store()`: small, correct by
the restart argument, and it turns every case into a clean stop. Refuse reads
as well until the restart, or at least document that reads after a failure
may see partial changes. Then 5.2 for transformations, so that bad input to a
counter does not stop the database: compute them before the first change.
5.3 only if a stop is ever too costly in practice.

In all cases, also clear `x.transNodes` at `x.begin` (or assert that it is
empty), so that no path can write another transaction's nodes again.


## 6. Test plan

* The reproduction of 2.1 as a unit test: after the failing transaction,
  either every later transaction is refused (5.1) or the database shows
  neither `/a = a1` nor writes it in a later record (5.2), and a restart gives
  the state before the failing transaction.
* A put that fails on a read error: a test stream that refuses one read
  (as `CutStream` refuses reads below the cut), a transaction whose second
  put loads that node; the same checks. With Level 4 in place, the same with
  an evicted node.
* An exception in `store()`: a test stream that fails an append; the
  database must stop, and a restart must give the state before the
  transaction (or after it, if its record is complete in the stream).
* With assertions on: no `two canonical objects` after any of these.
* The gates, and item 001's conformance, which checks that every committed
  transaction is a step of the model: a fix must not change any stream when
  nothing throws (StreamDigest).


## 7. When

Not now: the fix lives in `Db.executeInner`, which item 001 is changing
(R8, and the J work packages next), and today nothing triggers it in normal
operation. It must be in place before item 001's J3, when the writer starts
loading evicted index nodes (M49). A good moment is between two of item 001's
commits, as a small change of its own, together with item 002's ordinal patch,
which touches `Db.executeInner` too.
