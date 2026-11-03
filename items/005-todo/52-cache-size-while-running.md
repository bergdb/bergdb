005-52. Change the cache size while the database runs
=====================================================

Status: open (reopened by Frans, 2026-10-29: one point of "Done when" is
left, the pause probe with a lowered budget; see Left to do. The API is
done: option B, decided by Frans and implemented with 005-53 on
2026-10-28; see Outcome). Planned for release 2026.2: the probe's two
properties, six runs in night 1's quiet block, the table (see Plan for
2026.2). Kind: fix. Created 2026-10-26.

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
* Fixed in `988fe1a` (005-65's commit, 2026-10-29): `Eviction.sweep`
  computes the trigger under the monitor that `setBudget` holds. Before, a
  batch that ended while `setBudget` lowered the budget could put back the
  old budget's trigger, and the decrease then waited until the resident
  bytes passed the old budget or another batch ended (005-80). Test:
  `Eviction.testSetBudgetAtBatchEnd` (2026-11-03).


Left to do
----------

Reopened by Frans, 2026-10-29 ("Reopen 005-52, ensure it is clear what is
left to do."). One point of "Done when" is not met: no get or commit
waits longer while the resident bytes converge to a lowered budget than
with a fixed budget. The first step measured the convergence (47 s from
664 to 132 MB, batches of at most 2.2 ms and gets of at most 6.1 ms under
ZGC), not this comparison. The steps:

1. The probe. `java/stress/PauseProbe.java` (009-03, section 1) cannot
   change its budget during a run. Add two properties, for example
   `lower=MB` and `lowerAt=S`: S seconds into each phase the probe calls
   `Db.setCacheSizeIndicator` with the lower budget (or
   `Database.setCacheSizeInMb`, if the probe moves to the Pub API).
   Without them the probe runs as now, so that its earlier tables stay
   comparable. The setter exists only since `fd8f513`; the probe reaches
   it by reflection, as it does `CacheStats`, so that one compiled copy
   still runs on 2026.1's jar.
2. The runs, in a quiet block on F53 (s1 too if it is quiet), on one jar
   from `main`, with ZGC and with G1, 1M keys, 4 readers, the default
   phases (`tsize=1,1000`, 60 s each): (a) a fixed budget of 100 MB, above
   the about 55 MB the startup distance pins; (b) a budget of, for
   example, 400 MB, lowered to 100 MB 10 s into each phase. Four runs,
   about 15 minutes. Raw output outside the repo; the script and the
   table here.
3. The comparison. For each collector and phase: the p99.9 and the
   longest wait of the gets and the commits in (b) against (a), the
   longest batch, the time until the resident bytes reach the new budget,
   and the GC log beside each long wait (with ZGC a long wait is
   BergDB's own, 010-P1).

Done when the table is here and no wait in (b) is longer than in (a)
beyond the spread between two runs of (a); then the entry closes. If one
is longer: its cause, and a proposal for Frans, before any change to
`java/`.


Plan for 2026.2
---------------

Written 2026-11-03 for 016-05 (W4), by Left to do's three steps, with two
changes:

* **Six runs, not four.** Left to do's "Done when" compares (b) with (a)
  "beyond the spread between two runs of (a)", so each collector has two
  runs of (a), one before and one after (b): ZGC a1, b, a2, then G1 a1, b,
  a2. About 17 minutes, not 15.
* **Window 2.** Frans, 2026-11-03, 15:40: "try your best to finish this
  work by 07:00 tomorrow in the morning". The quiet block of night 1 is
  in window 2 only, from `night.sh`'s end (about 03:00) to 06:15, after
  005-65's rerun (016-05, section 6). The probe's change is committed
  before the release commit, by about 22:00.

The steps, by agent F2 (016-05), after 005-65's step 1, in
`/Users/f/fl/bench/016/005-52/repo` (a clone of `main`):

1. **The probe's properties** (0.75 hours), `java/stress/PauseProbe.java`:
   * `lower=MB` (default 0: off) and `lowerAt=S` (default 10). Without
     `lower` the probe runs and prints exactly as now, so that its earlier
     tables (009-03, 005-46) stay comparable and W7 can run it on 2026.1's
     jar (016-10).
   * With `lower`, in each phase: at its start the probe sets the budget
     back to `budget`; `lowerAt` seconds in, the writer's loop, between two
     commits, sets it to `lower`. Both by reflection, `Db`'s
     `setCacheSizeIndicator(long)` (since `fd8f513`), found once at the
     start; a jar without it fails the probe at once with a clear message,
     and only when `lower` is set.
   * At the lowering, a sampler thread reads the resident bytes every
     10 ms (by reflection, `db.internal().cache().residents().bytes()`,
     found once), until they are at most `lower` or the phase ends.
   * The header line gets ` lower=L MB lowerAt=S s` when `lower` is set.
     Each phase gets one line more, before its `gets` line:
     `  lowered: budget B to L MB at uptime U s, resident R MB; reached
     in X s` (or `; not reached, resident R MB at the phase's end`).
   * The Javadoc's list of properties names both.
2. **The probe's smoke** (0.1 hours, untimed, by day): in the clone,
   `sh java/build.sh`, then `java -Xmx512m -cp
   java/build/bergdb.jar:java/build/stress -Dkeys=20000 -Dseconds=3
   -Dbudget=8 -Dlower=2 -DlowerAt=1 -Ddir=/Users/f/fl/bench/016/005-52/smoke-db
   bergdb.core.PauseProbe` prints two `lowered:` lines and `PAUSE PROBE
   OK`; the same without `lower` prints no `lowered:` line.
3. **The gate**: `java/before-commit.sh` (`BEFORE COMMIT OK`; `build.sh`
   compiles `java/stress/`). No level script: no mechanism changes.
4. **The review** (016-05, section 5): 0.5 hours of another agent: that
   the probe without `lower` is unchanged, the reflection, the sampler's
   end, the writer's timing (the setter is called outside the timed
   commit).
5. **The hand-off** of the probe (016-05, section 4); the coordinator
   commits it, by about 22:00. Agent F1's line for 005-80 in this entry's
   Outcome comes in its own hand-off.
6. **The step script**, [night/lowered.sh](52-cache-size-while-running/night/lowered.sh),
   and its parser, [night/sum52.py](52-cache-size-while-running/night/sum52.py),
   written with this plan on 2026-11-03 in the main tree's `night/`
   (night scripts are the agents' to write there; 016-05, section 3). F2
   reads them against the probe as made, and adjusts them to its output
   (0.2 hours). `sum52.py` was tried on made-up outputs of the format
   below (12 rows, complete); `lowered.sh` only by `sh -n`. What they do:
   * `# minutes: 25` on its second line; the header says what, the runs,
     the time (about 17 minutes), the usage, the outputs and the exit
     status, as `budget.sh` does.
   * It uses only `R=/Users/f/fl/bench/016/005-52/run`: `bergdb.jar`,
     `stress/` and `jar.txt` (the commit and the jar's SHA-256), from
     step 7, and `/opt/homebrew/opt/openjdk/bin/java` (JDK 27). It
     compiles nothing. It exits 2 if one of these is missing, or if
     `stress/bergdb/core/PauseProbe.class` lacks the string `lowerAt`.
   * The runs, in this order, one JVM each, the database in `$R/db`
     (the probe empties it first):
     * `zgc-a1`, `zgc-b`, `zgc-a2` with `-XX:+UseZGC`; `g1-a1`, `g1-b`,
       `g1-a2` with `-XX:+UseG1GC`;
     * all: `-Xms2g -Xmx2g -XX:+AlwaysPreTouch
       -Xlog:gc*,safepoint:file=$OUT/RUN.gc.log:uptime,level,tags
       -Dkeys=1000000 -Dvalsize=100 -Dreaders=4 -Dseconds=60
       -Dtsize=1,1000 -Ddir=$R/db`;
     * (a): `-Dbudget=100`, above the about 55 MB that the default
       startup distance pins; (b): `-Dbudget=400 -Dlower=100 -DlowerAt=10`.
   * The deadline, as `budget.sh`'s: a run that would start with less
     than 4 minutes left is skipped and counted as failed; a JVM still
     running at 24 minutes is killed.
   * The outputs, outside the repository: `$OUT=$R/out`: `RUN.txt`,
     `RUN.gc.log`, `runs.txt` (each run's start, end and last line), and
     `summary.txt` from `python3 night/sum52.py $OUT`.
   * `sum52.py` prints one row per run and phase: the run; the phase; the
     gets' count, p99.9 and max; the commits' count, p99.9 and max; the
     longest batch so far (`ms at most` of the eviction line); for (b),
     the lowering's `reached in X s`; and the five longest gets' and
     commits' uptimes, for the GC log. It exits 1 if a run's phases are
     missing.
   * The exit status: 0 if all six runs printed `PAUSE PROBE OK` and the
     summary has 12 rows, with a `lowered` value in each of (b)'s 4; then
     it prints `lowered: OK`, else `lowered: FAILED, N problems`, exit 1.
   * `SMOKE=1`: `$OUT=$R/smoke`, `-Xms512m -Xmx512m`, `-Dkeys=20000
     -Dseconds=3`, (a) `-Dbudget=4`, (b) `-Dbudget=8 -Dlower=2
     -DlowerAt=1`, no skip; about a minute; the same checks of the
     summary; it prints `lowered (SMOKE): OK`.
   * Not `performance.sh`, so no `FORCE=1`.
7. **The prep** (0.2 hours), after the probe's commit: in the clone,
   `git pull -q` (to `main` with the probe), `sh java/build.sh`; copy
   `java/build/bergdb.jar` and `java/build/stress/` to `$R`; write
   `$R/jar.txt` (`git rev-parse HEAD`, `shasum -a 256 bergdb.jar`).
8. **READY** (0.1 hours): `SMOKE=1 sh night/lowered.sh` from the main
   tree's path prints `lowered (SMOKE): OK`; then `touch
   night/lowered.sh.READY`, and its last line and the time in this
   entry's Log (in the clone's next hand-off, or by the coordinator).
   Planned by 20:30; at the latest by 01:30 (016-05, section 6).
9. **The block** (window 2): the conductor's step `52-lowered`, after
   `65-rerun`. The session and the agents are idle.
10. **The morning** (1 hour, F2 or another agent): the table here, from
    `summary.txt`, one row per run and phase, as 009-03's; the comparison
    for each collector and phase: (b)'s p99.9 and longest wait of the gets
    and of the commits against the larger of a1 and a2, and the spread
    between a1 and a2; the time to reach the lowered budget; for each wait
    of (b) above (a)'s, the GC log at its uptime. Then:
    * no wait of (b) longer than (a)'s beyond that spread: Left to do's
      point is met, the entry closes (Outcome, Status "done");
    * one longer: its cause, and a proposal for Frans, before any change
      to `java/` (a stop, 016-05, section 8); the entry stays open, and
      the notes (016-03) name it.
    A run marked `NOT QUIET` in the conductor's `results.txt` is said in
    the table and does not close the entry by itself.

Size: about 3 agent-hours (0.85 for the probe and its smoke, 0.5 the
review, 0.6 for the scripts, the prep and READY, 1 in the morning), and 25
minutes of the block.
Depends on the probe's commit for steps 7 and 8, and on 005-65's step
running first in the block. Stop for Frans: only if a wait is longer
(step 10).

**State** (2026-11-03, 16:52, F1): steps 1 to 8 done. The probe is in
`main` (`87d1e2c`); `$R` = `/Users/f/fl/bench/016/005-52/run/` holds
`bergdb.jar`, `stress/` and `jar.txt` from `c960c34`; the smoke printed
`lowered (SMOKE): OK`, and `night/lowered.sh.READY` is written (16:51).
Next: step 9, the conductor's step `52-lowered` in window 2 (after
`65-rerun`; its `steps.txt` line in 016-05, section 6), then step 10 in
the morning, from `$R/out/summary.txt`. To resume: step 10, or the
conductor's `status.txt` if the block has not run.

Log
---

2026-11-03. Planned for release 2026.2 (016-05): `PauseProbe`'s `lower`
and `lowerAt`, six runs (two of the fixed budget per collector, for the
spread) in night 1's window 2, the table in the morning. Nothing changed
yet.

2026-11-03, 16:20 to 16:28, by F1 (016-05; the coordinator gave this part
to F1), in `/Users/f/fl/bench/016/005-52/repo`, steps 1 and 2:

* **The probe's properties** (step 1), `java/stress/PauseProbe.java`:
  `lower=MB` (default 0, none) and `lowerAt=S` (default 10). With `lower`:
  the start refuses a `lowerAt` outside 0 to `seconds` - 1, and finds by
  reflection, once, `Db.setCacheSizeIndicator(long)` and the resident
  bytes' path (`internal()`, `cache()`, `residents()`, `bytes()`); a jar
  without them fails the probe there with a message that names them. Each
  phase sets the budget back to `budget` before its readers start;
  `lowerAt` seconds in, the writer's loop, before it builds its next
  transaction and outside the commit's timing, makes a `Lowering`: the
  resident bytes then, the budget set to `lower`, and a sampler thread
  (daemon) that reads the resident bytes every 10 ms until they are at
  most `lower` or the phase's `stop`; the phase joins it after the readers
  and fails if it threw. The header gets ` lower=L MB lowerAt=S s`, and
  each phase, before its `gets` line, `lowered: budget B to L MB at uptime
  U s, resident R MB; reached in X s` (or `; not reached, resident R MB at
  the phase's end`). Without `lower` nothing of this runs: no reflection,
  no setter call, the same lines. The class Javadoc names both
  properties.
* **The smoke** (step 2, untimed, JDK 27): `-Dkeys=20000 -Dseconds=3
  -Dbudget=8 -Dlower=2 -DlowerAt=1`: two `lowered:` lines ("budget 8 to 2
  MB at uptime 1.507 s, resident 7 MB; reached in 0.017 s"; in the phase
  tsize=1000 "not reached, resident 4 MB at the phase's end") and `PAUSE
  PROBE OK`. Without `lower`: no `lowered:` line, the header as before,
  `PAUSE PROBE OK`. With `lowerAt=3` and `seconds=3`: `PAUSE PROBE FAILED:
  java.lang.IllegalArgumentException: lowerAt=3 must be from 0 to less
  than seconds=3`. Outputs in `/Users/f/fl/bench/016/005-52/smoke/`.
* **`sum52.py` against the probe as made** (step 6's reading): on six
  copies of the two smoke outputs (a outside, b with `lower`) it parses
  the header, the phases, the `lowered:` lines (`reached` 0.017 and "not
  reached"), the latencies and the eviction line: 12 rows, `complete`,
  exit 0. No change to `sum52.py` or `lowered.sh` is needed for the
  probe's format.
* **The gate** (step 3): `java/before-commit.sh`, 16:43 to 16:45: `BEFORE
  COMMIT OK (100 s)` (its build compiles `java/stress/`).

2026-11-03. Reviewed 2026-11-03 by the coordinator (H5, 016-05, section
5): no findings. Without `lower` no reflection and no new call; the
budget is reset each phase; the sampler ends on `stop` or when it reaches
the lower budget; a failure of the sampler fails the phase. Committed as
`87d1e2c`.

2026-11-03, 16:49 to 16:52, by F1, steps 7 and 8:

* **The prep** (step 7), by `/Users/f/fl/bench/016/005-52/prep.sh` (a
  fresh clone of `main`, as the work clone keeps its entry edits): `main`
  at `c960c34` (the probe's commit `87d1e2c` and one of documents), `sh
  java/build.sh`; `bergdb.jar` and `stress/` copied to `$R`; `$R/jar.txt`:
  `c960c34218409ff943e92be097f15aa08abfde8a` and the jar's SHA-256
  `665ef9ceeeb826caef74c486970e2437953bfadd7cb5904c0f25dd623eba7ed6`.
* **READY** (step 8): `SMOKE=1 sh night/lowered.sh`, from the main tree's
  path, 16:50:41 to 16:51:30 (F53 loaded, about 50): six runs OK, 2
  lowerings in each (b), the summary complete (12 rows); its last line
  `lowered (SMOKE): OK, 0 problems;
  /Users/f/fl/bench/016/005-52/run/smoke/summary.txt`. Then `touch
  night/lowered.sh.READY` (16:51).
