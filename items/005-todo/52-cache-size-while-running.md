005-52. Change the cache size while the database runs
=====================================================

Status: done (2026-10-28: option B, decided by Frans and implemented with
005-53; see Outcome; the pause probe of "Done when" left for a quiet
block). Kind: fix. Created 2026-10-26.

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


The first step, prepared for the quiet block (2026-10-27)
--------------------------------------------------------

By Claude (Opus 5.5, Claude Code), 2026-10-27 (006-09, W6.4). Not run
yet: [night/budget.sh](52-cache-size-while-running/night/budget.sh) is a
step for tonight's conductor (`# minutes: 45`, about 15 to 25 used; it
kills its JVM at 44), with `budget.sh.READY` written after a smoke test
(`SMOKE=1`, 40 s, all three runs `BUDGETBENCH OK`). It builds nothing: it
uses a jar built from HEAD `a6cd234` and the class compiled from
[night/BudgetBench.java](52-cache-size-while-running/night/BudgetBench.java),
both in `/Users/f/fl/bench/006-09/w6/night`.

What it measures. `BudgetBench` is not ScaleBench but loads the same
database in its own JVM (10M key24 keys, 1,000 puts a transaction,
node size 30, budget 665 MB). Then 2 readers (uniform gets) and a writer
(200 commits a second of 10 puts) run through five phases: warm (until
the resident bytes are steady), base (60 s), converge (`setBudget` to a
fraction of the resident bytes, until they are at most that; at most
300 s), after (60 s at the low budget) and raise (30 s back at 665 MB).
The load leaves only the latest tree resident, about 16 bytes a key by
the cache's count (smoke runs at 0.2M to 0.5M keys), so 665 MB is never
reached and the low budget is set from the resident bytes: about 160 MB
at 10M keys, if that holds. Three runs: ZGC to a fifth, G1 to a fifth,
ZGC to a half. With ZGC a long wait is BergDB's own (010-P1); G1 is the
default collector, and its pauses are in its GC log.

How to read the output (`night/out/`):

* `RUN.txt`, the line `converge:`: the resident bytes at the drop and the
  new budget; how long until the resident bytes reached it; the
  eviction thread's CPU time over that (ThreadMXBean, thread
  `bergdb-evictor`); the sweeps, objects released and sweep time over it
  (`Eviction.figures`, the writer's batches and the thread's together).
  The question-2 answer: if the convergence takes a fraction of a second
  of one thread, "batches at full speed" is gradual enough at this size;
  a 6 GB drop (the issue's example) is about 45 times the 130 MB evicted here.
* `RUN.txt`, the lines `gets, PHASE:` and `commits, PHASE:`: calls a
  second, the longest, and counts above 1 to 100 ms. Compare converge
  with base and after: the waits caused by the convergence are those
  above the other two phases' longest. Then `slowest gets` and `slowest
  commits`: the 15 longest calls, each with its time in seconds from the
  drop (negative before it).
* `RUN.csv`: a line every 100 ms (phase, seconds from the drop, resident
  bytes, budget, the eviction thread's CPU in ms, sweeps, objects
  released, sweep ms, longest sweep, and the gets and commits in the
  interval with the longest of each): the convergence's curve, and which
  intervals the long waits fall in.
* `RUN.gc.log` for the collector's pauses beside the long waits;
  `runs.txt` for the step's start, end and a line per run.

The smoke runs, on a busy F53 (load near 12) and at 0.2M keys, timed
nothing; they showed one thing to look for: a sweep of 45 ms in one run,
against the batch limit of 2 ms (`Eviction.BATCH_NANOS`). The night's
`converge:` line gives the longest sweep of each run.


Size and order
--------------

S to M: the method is small; question 2 decides the rest. After or with
005-51.


The first step, measured
------------------------

2026-10-28, 01:20 to 01:33, in 006-09's quiet block on F53 (jar `a6cd234`,
10M keys; [52-cache-size-while-running/night/out/](52-cache-size-while-running/night/out/)),
by Claude (Opus 5.5, Claude Code). The budget lowered in the middle of the
run by `setBudget`, from 664 MB resident:

| run | new budget | reached after | the eviction thread's CPU | longest batch | longest get | longest commit |
|---|---|---|---|---|---|---|
| ZGC, to a fifth | 132 MB | 47.0 s | 22.0 s | 2.18 ms | 6.09 ms | 38.4 ms |
| G1, to a fifth | 132 MB | 46.9 s | 26.3 s | 88.8 ms | 36.7 ms | 45.1 ms |
| ZGC, to a half | 332 MB | 0.31 s | 0.19 s | 2.22 ms | 4.12 ms | 28.5 ms |

Question 2: the resident bytes converge in bounded batches (2.2 ms under
ZGC), and gets stay short under ZGC. Under G1 a batch took 88.8 ms, most
likely a collection inside it; the commits' 28 to 45 ms are not yet
compared with a fixed budget's. So the step answers the convergence, and
leaves the comparison with a fixed budget for the fix.


Questions 1 and 3, the Pub API: options A to C
----------------------------------------------

By Claude (Opus 5.5, Claude Code), 2026-10-28 (006-10, W4.2), a reading of
`main` at `b1111f4`, together with 005-53's options, as both are a setting
changed while the database runs. The evidence is in 005-53's
[report.md](53-startup-distance-on-the-fly/report.md), sections 1, 2.2 and
4.

**What every option starts from.** `Eviction.setBudget(long)` sets the
budget (the high watermark), the low one (3/4 of it) and the trigger;
`Db`'s constructor gives it the builder's cache size, and also
`Cache3.setSizeIndicator`, whose value only a getter reads. No method of
`Db` reaches `setBudget`: only `db.internal().eviction()`, as
`Jmx.DbMonitor.setCacheSizeIndicator` does. The cache size changes no byte
of the stream (`level4.sh`'s EvictionInvariance).

* A decrease: the next commit's batch (at most 2 ms) or a reader's load
  wakes the eviction thread, which runs batches of at most 2 ms until the
  resident bytes are at most the new trigger, a waiting writer first.
  While they are over it by more than the gap between the watermarks, a
  load waits for the next batch, at most 2 ms (`Eviction.afterLoad`). The
  first step (above) measured it at 10M keys: 664 to 132 MB in 47 s with
  22 s of the thread's CPU, batches of at most 2.18 ms and gets of at
  most 6.09 ms under ZGC; 664 to 332 MB in 0.31 s. With no calls, nothing
  runs (005-51). A budget below the pinned bytes (the nodes changed since
  the startup position, of the order of the startup distance) is not
  reached: a sweep raises the trigger to them plus the gap.
* An increase: nothing to do; the resident bytes grow with the loads.
* Replicas: none; a replica is a stream of this database, the cache is
  the JVM's.

### A. Keep it as it is

The builder sets the cache size at start; JMX, through the core's
internals, changes it.

* API: none. Gives: nothing to build. Costs: 010-P6 stays broken; a
  change needs a restart. Effort: none.

### B. `void setCacheSizeInMb(int)` and `int getCacheSizeInMb()`, for the run (recommended)

A setter and getter on `Database`, beside `setRetainDuration`, with a
setter and getter in the core that JMX then uses too.

* API, in `pub/Database`:

      /**
       * Sets the cache size indicator in MB, the budget of the database's
       * cache, as DatabaseBuilder.cacheSizeInMb() does at start, clamped
       * the same way, to 4 to 100,000 MB. The new budget is in force when
       * the method returns. After a decrease the database evicts what it
       * holds above the budget in batches of at most 2 ms, which this call
       * and the database's commits and reads start, until the resident
       * bytes are at most the budget; reads may wait for a batch meanwhile,
       * at most 2 ms each. What the database must keep in memory is never
       * evicted and may exceed the budget. After an increase, the cache
       * grows as data is read. The setting is for this run only: it is not
       * stored, and a restart takes the builder's value, or its default, a
       * fifth of the JVM's maximum heap.
       */
      public void setCacheSizeInMb(int cacheSizeInMb);

      /** Returns the cache size setting in MB, the budget, not the memory
       *  the cache holds now. */
      public int getCacheSizeInMb();

* The core: `Db.setCacheSizeIndicator(long)` and `getCacheSizeIndicator()`
  (the builder's name), which set `Eviction`'s budget and `Cache3`'s
  indicator, and wake the eviction thread when the resident bytes are
  over the new trigger, so that an idle database gives the memory back
  too (work that the call starts, 010-P3). `Jmx.DbMonitor` calls them
  instead of reaching into `internal()`. Two methods more in `Db` (43 to
  45): settings belong to the Core API (010-P12), and the alternative,
  `pubimp` calling `db.internal()`, which says "for internal use only",
  would be a way around the layer, not an implementation on top.
* Persistence: none, as the retain duration (question 3). The cache size
  shapes no byte of the stream, so P2 does not need it there; it belongs
  to the machine, not to the data: its default is a share of the JVM's
  heap, and a stored size would follow a copied database into a smaller
  JVM; and storing it would need the meta block's reserved bytes and a
  rule for the builder's value against the stream's, 005-53's option C's
  trap.
* A stopping or stopped database: harmless, a field set; the Javadoc says
  "no effect after stop()". No exception needed.
* Tests: through `Database`, in memory: lower and raise the budget under
  reads and writes, the resident bytes at most the trigger after the
  convergence, and growing after a raise; the clamp; the value back at
  the builder's after a restart; with no calls after a decrease, the
  resident bytes still converge (the wake). Then this entry's "Done
  when": the pause probe of 009-03 with a lowered budget against a fixed
  one, and `level4.sh`.
* Gives: 010-P6 for the cache size, with the convergence the first step
  measured. Costs: two core methods.
* Effort: S for the code and tests; M with the pause probe, in a quiet
  block.

### C. B, kept in the stream

As B, and the setting written to the stream, in the meta block's reserved
bytes (as 005-50 added the node size, no new version), so that a restart
keeps it.

* Needs a rule for which wins at a start, the builder's value or the
  stream's; an application that passes the builder's value every start
  makes the stored one moot, and one that does not inherits a size chosen
  for another machine or heap.
* Makes a setting that changes no byte of the data change the stream's
  bytes, against the line 010-P2 draws.
* Effort: M, with a format field and its tests.

### Recommendation

B: `setCacheSizeInMb` and `getCacheSizeInMb` on `Database`, clamped as the
builder, for the run only, through a setter and getter in `Db` that JMX
uses too, waking the eviction thread after a decrease. Decide and build it
with 005-53's E, as one pattern: a setter that returns when the setting is
in force; a getter that gives the setting, not the state converging to
it; convergence by the database's ordinary work in bounded pieces; kept in
the stream only if the setting shapes the stream's bytes (the report,
section 4). Question 2 is answered by the first step for the convergence;
the comparison with a fixed budget is part of the fix.


Questions for Frans
-------------------

1. `Database.setCacheSizeInMb(int)` and `getCacheSizeInMb()`, clamped to 4
   to 100,000 MB as the builder? Recommended: yes (B).
2. Kept in the stream? Recommended: no, for the run, as the retain
   duration; a restart takes the builder's value.
3. In the core, `Db.setCacheSizeIndicator` and `getCacheSizeIndicator`
   (two more public methods), used by JMX too, rather than `pubimp`
   reaching into `db.internal()`? Recommended: yes.
4. The setter wakes the eviction thread after a decrease, so that an idle
   database converges too? Recommended: yes.
5. Decide and implement together with 005-53, one pattern? Recommended:
   yes, one commit.


Decision
--------

Frans, 2026-10-28, 12:32: "53 and 52. Yes, do this as recommended.", and
the smaller questions "as recommended". So: B, clamped to 4 to 100,000 MB
as the builder; for the run only, not kept in the stream; a setter and a
getter in `Db`, which JMX uses; the setter wakes the eviction thread after
a decrease; done together with 005-53, in one commit.


Outcome
-------

2026-10-28, by Claude (Opus 5.5, Claude Code), for 006-10, in a clone on
`8b37ad1`, together with [005-53](53-startup-distance-on-the-fly.md); the
code is one commit, `fd8f513`. Gates, StreamDigest and their files: in
005-53's Outcome.

* The API, in `pub/Database`: `void setCacheSizeInMb(int)` and
  `int getCacheSizeInMb()`. `DatabaseImp` clamps as the builder (4 to
  100,000 MB, one static method of `DatabaseBuilderImp` for both) and
  calls `Db.setCacheSizeIndicator`; the getter rounds
  `Db.getCacheSizeIndicator()` to MB. The Javadoc: in force when the call
  returns; after a decrease the database evicts in batches of at most 2
  ms, which the call and the commits and reads start, also when no call
  follows; reads may wait for a batch, at most 2 ms each; pinned state may
  exceed the budget; for this run only, a restart takes the builder's
  value; the pattern (a setting that changes the stream's bytes is kept in
  the stream, one that does not lasts for the run).
* The core: `Db.setCacheSizeIndicator(long)` and `getCacheSizeIndicator()`
  (Db's public methods from 43 to 45, 010-P12). The setter sets `Cache3`'s
  indicator and `Eviction.setBudget(Db, long)`, new: the budget as
  `setBudget(long)` sets it, then, with the capacity controller's schedule
  and an active database, a wake of the eviction thread if the resident
  bytes are over the new trigger: work that the call starts (010-P3). The
  getter is `Eviction.budget()`, as JMX read it. `Jmx.DbMonitor`'s
  `get`/`setCacheSizeIndicator` call them instead of `db.internal()`.
  Thread safety as the retain duration's setter: no write lock;
  `Eviction`'s fields are volatile and set under its monitor.
* A stopped or stopping database: the setter sets the values and does not
  wake the thread (it has ended or ends); it throws nothing, as
  `setRetainDuration`. The Javadoc says so ("After stop() the method has
  no effect").
* `DatabaseBuilder.cacheSizeInMb`'s Javadoc names the new setter.
* The tests:
  * `PubTester.testSetCacheSizeInMb` (unit): the builder's 64 MB; 32 MB in
    force at once (the getter, `Db`'s getter, `Eviction`'s budget and
    `Cache3`'s indicator); 1 gives 4 and 200,000 gives 100,000; nothing
    written to the stream; a call after `close()` throws nothing; a
    restart with the builder at 64 has 64.
  * `PubTester.testLoweredCacheSizeWhileIdleF` (f): 20,000 values of 1 kB
    written with a budget of 100 MB (about 20 MB resident), the cache size
    lowered to 4 MB and no other call: the resident bytes are at most 4 MB
    within 5 s (about 0.2 s here).
  * `CapacityTester.testBudgetLoweredAndRaisedUnderReads` (unit, core):
    2000 values of 300 bytes, every key read with a budget of 10 MB; the
    budget lowered to a quarter of the resident bytes; from the second
    round of random reads on, the resident bytes are at most the budget
    plus 20 kB; the budget raised again, reading every key grows them past
    twice the low budget.
  * `CapacityTester.testBudgetLoweredWhileIdle` (unit, core): as the one
    before, and after the decrease no other call: at most the budget
    within 2 s.
  * Without the wake (a mutation in a copy) the three convergence tests
    fail: the resident bytes stay where they were (924,984 bytes against a
    budget of 231,246; 19,996,280 against 4 MB). Under reads too, as every
    value is resident, so the reads load nothing and wake nothing.
* StreamDigest identical (005-53's Outcome): no configuration calls the
  setter, and the cache size changes no byte (EvictionInvariance in
  `level4.sh`).

Left: "Done when"'s pause probe of 009-03 with a lowered budget against a
fixed one (no get or commit waiting longer), for a quiet block; the first
step's runs measured the convergence (47 s from 664 to 132 MB, batches of
at most 2.2 ms and gets of at most 6.1 ms under ZGC), not the comparison.
