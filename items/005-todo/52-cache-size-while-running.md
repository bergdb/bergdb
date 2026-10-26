005-52. Change the cache size while the database runs
=====================================================

Status: open. Kind: fix. Created 2026-10-26.

Found in [010-01](../010-principles/01-principles.md), 010-P6 ("No
interruption for changes"); registered at Frans's request (2026-10-26:
"Yes, register an entry for that."), after: "Cache size. That should be
possible to change while the database is running without disruptions, just
gradual changes. Gradual convergence to the new setting."


The issue
---------

The Pub API sets the cache size only at start
(`DatabaseBuilder.cacheSizeInMb`); a change needs a restart. That is a
deviation from 010-P6: settings change while the database runs, without
stopping it or the application's calls.

The core can change it already. `Eviction.setBudget` sets the capacity
controller's budget, its low watermark (3/4 of it) and its trigger, used
from the next transaction boundary or load. `Jmx.DbMonitor`'s
`setCacheSizeIndicator` calls it, with `Cache3.setSizeIndicator`. The Pub
API has no such method.

What a lower budget does today, by reading the code (not measured): the
next commit runs one batch (at most 2 ms, `Eviction.BATCH_NANOS`) and
wakes the eviction thread, which runs batches back to back until the
resident bytes are at most the new trigger, letting a waiting writer go
first. No single wait is long (010-P1), but the thread may run for a long
time at full speed: to go from 8 GB to 2 GB, it evicts 6 GB at once. A
higher budget needs no work.


The scope
---------

A Pub API method that changes the cache size of a running database, with
no disruption: the resident bytes converge gradually to the new size
(010-P1, 010-P4). The work of the convergence is triggered by the calls,
as all eviction (010-P3, [005-51](51-eviction-on-calls.md)).


Questions
---------

1. The method: `Database.setCacheSizeInMb(int)`, beside
   `setRetainDuration`, and a getter? The same clamping and default as
   `DatabaseBuilder.cacheSizeInMb`?
2. "Gradual": is a convergence by batches at full speed, as today, gradual
   enough? Or should a lower budget be approached in steps, a share per
   call, as 010-P4 asks of piggy-backed work? With what rate, and what
   happens to loads while the resident bytes are above the new budget?
3. Is the new size kept in the stream, as the startup distance is, or only
   for this run? `cacheSizeInMb` is not stored today.
4. 005-51 changes when the eviction thread works; this entry should follow
   its answer.


Done when
---------

* The Pub API changes the cache size of a running database; a test
  lowers and raises it under reads and writes, and the resident bytes
  converge to the new budget.
* No get or commit waits longer than with a fixed budget, in the pause
  probe of 009-03 with a lowered budget.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`; `level4.sh` passes.


First step
----------

Answer question 2 with a measurement: lower the budget by `setBudget` in
the middle of a ScaleBench run, and record the eviction thread's work and
the longest waits of gets and commits until the resident bytes reach it.


Size and order
--------------

S to M: the method is small; question 2 decides the rest. After or with
005-51.
