028-16. Fix: a refused second start of one Db closes the database the first started
==================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-16 by Frans Lundberg.

What: `DatabaseImp.createAndStart(Db)` (package-private) closes the `Db`
in its catch when `db.start()` refuses it. If it is called twice on one
`Db`, `Db.start()` refuses the second call (`IllegalDbStateException`),
and that call's catch closes the database that the first call started,
against `Db.start()`'s Javadoc ("nothing is closed then"). Since 028-07
the close can also come while the first call's index manager starts.

Why: only BergDB's own tests can make the two calls; the Pub API builds a
new `Db` for each start (`DatabaseBuilderImp`). Low priority, but the code
and the Javadoc disagree.

Done when: a refused call closes nothing that another call started (for
example, the catch closes the `Db` only when this call's `db.start()`
began the start), with a test of two calls on one `Db`; or the Javadoc
says what happens. `java/before-commit.sh` prints BEFORE COMMIT OK.

Source: 028-07, section "what the lock guarded" (two `createAndStart()`
calls on one `Db`).


Findings
--------

* The fault was as described: `DatabaseImp.createAndStart(Db)`
  (`java/src/bergdb/pubimp/DatabaseImp.java`, line 119 of 8ae38f65, in
  its catch) called `db.close()` for any exception, also for the
  `IllegalDbStateException` of a second call's refused `db.start()`. A new
  test shows both forms: a second call after the first returned stopped the
  first's database (its next put threw `DbStoppingException`); a second
  call from inside the first, after its `db.start()` (028-07's window),
  made the first call's own start fail in its index manager's scan.
* What `Db.start()` leaves when it throws: either it refused the call
  (`assertStateIsZero()`, before its `try`: the state is not ZERO, as
  another call started the `Db`, or `stop()` was called) and closed
  nothing; or the start itself failed, and `closeAfterFailedStart()` has
  closed the storage and set `closeBegun` and `closeDone`. In the second
  case `createAndStart()`'s `db.close()` did nothing but wait for the
  done close and, after a failed storage close, add a second, wrapped copy
  of the close's failure to the exception (the start had added the
  `IOException` itself as suppressed). So a close is needed only when
  something throws after this call's `db.start()` returned.


What was done
-------------

`createAndStart()` closes the `Db` only when its own `db.start()`
returned (a local `started`, set right after it), and makes the
`DatabaseImp` after `db.start()` instead of before, so that nothing that can
throw comes before `db.start()`; its Javadoc and comment say so, and the
refusal's `@throws` says "nothing is closed then". `Db` is unchanged. The
`DatabaseImp` constructor only makes the object's own fields (an empty
`IndexManager`, a map, the converter) and does not use the `Db`, so the
order does not matter to it.

Why it is safe, by interleaving (calls A and B on one `Db`):

* `Db.start()` checks and changes the state under both of the `Db`'s locks
  (`writeLock`, `readSync`), and its whole start runs under them: of all
  calls on one `Db`, at most one `db.start()` returns, and only that call
  sets `started` and may close. Every other call is refused and closes
  nothing, whatever the other call is doing: in its `db.start()`, in its
  hook, in its index manager's start, failed, or returned.
* A's `db.start()` throws (the start failed): it closed its storage
  itself, as before; A now skips the second close, which did nothing (see
  Findings). B is refused (state STOPPING) and closes nothing.
* A's `db.start()` returned and something after it throws (the
  `DatabaseImp`'s construction, the test hook, the index manager's start):
  A closes the `Db`, as before (005-32). `testExceptionAfterStartClosesDb`
  still passes.
* Before A's `db.start()` only `System.nanoTime()` and local stores run:
  no path leaves the `Db` unstarted and open. Before, an exception from
  `new DatabaseImp(db)` before `db.start()` closed the `Db`; now that
  construction comes after it, so the close for the Pub API's start
  (`DatabaseBuilderImp.start()`, one call per `Db`) is kept.
* `stop()` before a call: refused, nothing closed by the call; `stop()`'s
  own close runs as before. Before, the refused call waited for that close.
* The Pub API builds a new `Db` for each start (`DatabaseBuilderImp`): its
  starts take the same path as before but for the skipped no-op close of a
  start that threw.

The test: `PubTester.testSecondStartOfOneDbClosesNothing`, two cases: the
second call after the first returned, and from `testHookAfterStart` inside
the first. The refused call throws `IllegalDbStateException` with nothing
suppressed; the first's database takes a put and a sync, closes, and a
restart on a copy of its stream reads the put. Both cases failed before the
change, as described in Findings.

Gates: `java/before-commit.sh` BEFORE COMMIT OK, `java/stress/level1.sh`
LEVEL 1 OK.


Log
---

2026-11-16. Registered by coord-1116, from 028-07.

2026-11-16. Taken by an agent of coord-1116 (in progress), in a clone on
branch 028-16-second-start.

2026-11-16. Done: a refused call closes nothing; the close only after the
call's own `db.start()` returned; a test of two calls on one `Db`; BEFORE
COMMIT OK, LEVEL 1 OK; by an agent of coord-1116 (Claude, Opus 5.5).
