005-52. Change the cache size while the database runs
=====================================================

Status: done (2026-11-05). Reopened by Frans on 2026-10-29 for one point
of "Done when", the pause probe with a lowered budget (Left to do); the API
was done with 005-53 on 2026-10-28 (Outcome). The night run of 2026-11-04
found the first large transaction after a decrease waiting about as long
as the convergence, through its warmup's loads (Results, 2026-11-04
night). Frans decided option B on 2026-11-04 (Decision, 2026-11-04): the
warmup does not wait for eviction; done in `8defe65` (Option B, done). The
six runs again, on s1 as F53 was not quiet (Results, 2026-11-04 evening):
no wait from the lowering on is longer than with a fixed budget; the four
LONGER verdicts all come before the lowering, the collector's and the
machine's. Closed on the coordinator's reading of the rule (The verdict,
there); Frans may reopen it if he reads the rule otherwise. Kind: fix.
Created 2026-10-26.

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
uses a jar built from HEAD `e747323` and the class compiled from
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

2026-10-28, 01:20 to 01:33, in 006-09's quiet block on F53 (jar `e747323`,
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
`main` at `f34f31f`, together with 005-53's options, as both are a setting
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
`077afea`, together with [005-53](53-startup-distance-on-the-fly.md); the
code is one commit, `decc677`. Gates, StreamDigest and their files: in
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
* Fixed in `52aeb04` (005-65's commit, 2026-10-29): `Eviction.sweep`
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
   comparable. The setter exists only since `decc677`; the probe reaches
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
     `setCacheSizeIndicator(long)` (since `decc677`), found once at the
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
`main` (`4d74c19`); `$R` = `/Users/f/fl/bench/016/005-52/run/` holds
`bergdb.jar`, `stress/` and `jar.txt` from `17270d1`; the smoke printed
`lowered (SMOKE): OK`, and `night/lowered.sh.READY` is written (16:51).
Next: step 9, the conductor's step `52-lowered` in window 2 (after
`65-rerun`; its `steps.txt` line in 016-05, section 6), then step 10 in
the morning, from `$R/out/summary.txt`. To resume: step 10, or the
conductor's `status.txt` if the block has not run.

**State** (2026-11-04): steps 9 and 10 done (Results, 2026-11-04 night),
the markers `lowered.sh.READY` and `.DONE` removed. A wait of (b) is
longer than (a)'s beyond the spread: the first large transaction after the
decrease. So, by step 10, a stop for Frans (016-05, section 8): its cause
and a proposal are in Results; the entry stays open, and the notes
(016-03) are to name it. No change to `java/` before his decision.


Results, 2026-11-04 night
-------------------------

From [night/lowered.sh](52-cache-size-while-running/night/lowered.sh), the
conductor's step `52-lowered` in window 2 of night 1 of release 2026.2
(016-02, 016-05 section 6): 2026-11-04, 03:43 to 03:56, exit 0, `lowered:
OK, 0 problems`; six runs `PAUSE PROBE OK`, two lowerings in each (b),
12 of 12 rows. The jar of `17270d1` (SHA-256 `665ef9ce`), JDK 27.

**Not quiet.** After 005-65's step the conductor waited 30 minutes for a
quiet machine and then started the step anyway ("NOT QUIET after 1800s"
in its `results.txt`); the load was 2.52, 2.63 and 3.16 (1, 5 and 15
minutes) at the start. What used the machine is not recorded. So the
spread of (a) and a single long wait may be the machine's; that is said
for each wait below.

The raw outputs stay out of the repository (013-01, section 4): each
run's text and GC log, `runs.txt` and `summary.txt` in
`/Users/f/fl/bench/016/005-52/run/out/`; the conductor's record in
`/Users/f/fl/bench/016/night1/out/52-lowered.txt` and `results.txt`.

Per run and phase, 1M keys, 4 readers, 60 s a phase; times in ms. Batch:
the longest eviction batch so far in the run. Reached: seconds from the
lowering (budget 400 to 100 MB, 10 s into the phase, the resident bytes at
398 or 399 MB) to the resident bytes at most 100 MB. The resident bytes
at each phase's end: 99 MB.

| Run | Phase | Gets | Gets p99.9 | Gets max | Commits | Commits p99.9 | Commits max | Batch | Reached |
|---|---|---|---|---|---|---|---|---|---|
| zgc-a1 | tsize=1    | 40,885,665 | 0.02 | 14.05 | 3,479,175 |  1.83 |   8.27 |  8.26 | -     |
| zgc-a1 | tsize=1000 | 30,465,671 | 0.03 | 14.04 |     4,152 | 20.97 |  38.87 |  8.26 | -     |
| zgc-b  | tsize=1    | 43,829,973 | 0.02 | 12.31 | 3,454,954 |  1.83 |  10.95 |  2.15 | 0.206 |
| zgc-b  | tsize=1000 | 39,837,025 | 0.03 |  8.71 |     4,586 | 16.78 | 194.94 |  2.50 | 0.197 |
| zgc-a2 | tsize=1    | 40,569,046 | 0.02 |  3.36 | 3,393,036 |  1.83 |   6.06 |  5.74 | -     |
| zgc-a2 | tsize=1000 | 30,054,221 | 0.03 | 11.96 |     4,185 | 29.36 |  40.55 |  5.74 | -     |
| g1-a1  | tsize=1    | 41,541,480 | 0.02 | 38.21 | 3,721,897 |  1.31 |  36.24 | 35.48 | -     |
| g1-a1  | tsize=1000 | 31,994,493 | 0.03 | 22.21 |     4,392 | 29.36 |  36.50 | 35.48 | -     |
| g1-b   | tsize=1    | 46,602,871 | 0.02 | 45.26 | 3,802,186 |  1.31 |  45.26 | 35.00 | 0.098 |
| g1-b   | tsize=1000 | 42,700,403 | 0.02 | 29.15 |     5,016 | 29.36 |  96.83 | 35.00 | 0.106 |
| g1-a2  | tsize=1    | 42,111,595 | 0.02 | 44.07 | 3,702,656 |  1.31 |  44.09 | 34.87 | -     |
| g1-a2  | tsize=1000 | 31,808,216 | 0.03 | 25.05 |     4,389 | 33.55 |  37.15 | 34.87 | -     |

**(b) against (a).** `sum52.py` marks a value of (b) LONGER when it is
above the larger of a1 and a2 by more than their spread, |a1 - a2|. Every
p99.9 of (b), of the gets and of the commits, is ok. The longest waits,
in ms, and when (b)'s came, by the probe's uptimes of the five longest and
of the lowering:

| GC | Phase | Longest | a1 | a2 | b | Spread | Verdict | (b)'s, when |
|---|---|---|---|---|---|---|---|---|
| ZGC | tsize=1    | get    | 14.05 |  3.36 |  12.31 | 10.69 | ok     |                           |
| ZGC | tsize=1    | commit |  8.27 |  6.06 |  10.95 |  2.21 | LONGER | 4.7 s before the lowering |
| ZGC | tsize=1000 | get    | 14.04 | 11.96 |   8.71 |  2.07 | ok     |                           |
| ZGC | tsize=1000 | commit | 38.87 | 40.55 | 194.94 |  1.68 | LONGER | began at the lowering     |
| G1  | tsize=1    | get    | 38.21 | 44.07 |  45.26 |  5.86 | ok     |                           |
| G1  | tsize=1    | commit | 36.24 | 44.09 |  45.26 |  7.85 | ok     |                           |
| G1  | tsize=1000 | get    | 22.21 | 25.05 |  29.15 |  2.84 | LONGER | 9.2 s before the lowering |
| G1  | tsize=1000 | commit | 36.50 | 37.15 |  96.83 |  0.65 | LONGER | began at the lowering     |

**What the four LONGER verdicts mean.** `sum52.py` compares a phase's
longest wait, wherever in the phase it came; two of the four came before
the lowering, with (b)'s budget still at 400 MB.

1. **ZGC, tsize=1000: a commit of 194.9 ms, the decrease's.** The lowering
   at uptime 74.103 s, with 399 MB resident; the commit ended at 74.298 s,
   so it began at 74.103 s: the first transaction after the lowering, which
   the writer's loop starts right after it. The resident bytes reached
   100 MB 0.197 s after the lowering (the probe's sampler reads them every
   10 ms): the commit lasted about the whole convergence. No ZGC pause or
   allocation stall in between (pauses of 0.012 ms at 74.068 and 74.372 s;
   every `Allocation Stalls` line 0): BergDB's own wait (010-P1). The next
   longest commit of the phase: 34.7 ms; (a)'s longest: 38.9 and 40.6 ms.
2. **G1, tsize=1000: a commit of 96.8 ms, the decrease's.** The same: the
   lowering at 73.767 s, the commit ended at 73.865 s (began at 73.768 s),
   the budget reached 0.106 s after the lowering. No G1 pause in between
   (the last before it ended at 73.708 s).
3. **ZGC, tsize=1: a commit of 10.95 ms, not the decrease's.** At uptime
   9.442 s, 4.7 s before the phase's lowering (14.095 s), with gets of 9.7
   to 11.1 ms ending at 9.441 to 9.443 s: one stall of about 11 ms of the
   readers and the writer together, with the budget at 400 MB. No ZGC
   pause then (0.007 ms at 9.358 s, 0.013 ms at 9.457 s). Most likely the
   machine, which was not quiet. It is above (a)'s 8.27 + 2.21 ms by
   0.47 ms.
4. **G1, tsize=1000: a get of 29.15 ms, not the decrease's.** At 64.587 s,
   0.8 s into the phase and 9.2 s before the lowering: a G1 pause, `Pause
   Young (Mixed)` of 28.9 ms ending at 64.587 s; four of the phase's five
   longest gets end then. Under G1 the longest gets are its pauses, as in
   009-03 (the longest G1 pauses of the runs: 38.0 ms in g1-a1, 45.0 in
   g1-b, 43.9 in g1-a2).

So the decrease made two long waits, one in each collector, and both are
the first commit of a transaction of 1,000 puts after it; the readers'
gets during the convergence are short (under ZGC the longest, 4.0 and
4.1 ms, at 74.275 and 74.283 s). With one put a transaction no commit
during the convergence is among the phase's five longest (under ZGC all
at most 4.7 ms). Noise does not begin a wait at the lowering and end it at
the convergence in both collectors, so the not-quiet machine does not
explain 1 and 2.

**The cause of 1 and 2**, from the code (the probe times `db.execute` as a
whole, not its parts). `Db.executeInner` first runs `warmup`: a get of
each of the transaction's keys, before it takes the write lock, so that
their loads go through `Eviction.afterLoad` as a reader's do (under the
write lock `afterLoad` returns at once). After the lowering the resident
bytes (399 MB) are over the new trigger (100 MB) by more than the gap
between the watermarks (25 MB): pressure. Under pressure each load wakes
the eviction thread and parks until its next batch has ended, at most
`LOAD_WAIT_NANOS`, 2 ms (009-02, step 3d: loads go at the pace of
eviction). A reader's get makes one or two loads, so it waits a few ms. A
transaction of 1,000 puts makes up to 1,000 gets in its warmup, each of
whose loads waits for a batch: each wait is bounded, their sum is not,
and the warmup goes at about one load a batch until the resident bytes
are below about 125 MB, nearly the whole convergence. So the Javadoc of
`Database.setCacheSizeInMb` ("reads may wait for a batch meanwhile, at
most 2 ms each") holds for each read, and a large transaction right after a
decrease waits about as long as the convergence: here 0.1 to 0.2 s for
300 MB. The same holds, by the code, for a large transaction while loads
outrun eviction with a fixed budget; these runs did not have that.

**Proposal, for Frans** (Left to do: "its cause, and a proposal for
Frans, before any change to `java/`"):

* **(A) Accept it and say so.** No code change. The Javadoc of
  `setCacheSizeInMb` adds that a transaction's own reads wait the same
  way, so that a large transaction right after a decrease waits about as
  long as the convergence. Left to do's point is then met as reworded,
  not as written.
* **(B) The writer's warmup does not park.** What: `Eviction.afterLoad`
  wakes the eviction thread for a load of a transaction's warmup but does
  not park for a batch, as it does not under the write lock. When: each
  load of a warmup under pressure. How the load listener tells a warmup's
  load from a reader's is part of the change (the warmup has its own
  `GetData`, `t.warmupGetData`). Effect: the resident bytes may rise by
  the nodes that one transaction's warmup loads, bounded by the
  transaction's size (`checkSize`), until its end runs a batch
  (`afterTransaction`) and the eviction thread goes on; the readers still
  go at the pace of eviction. Checked by a test that lowers the budget
  under a transaction of 1,000 puts and bounds its commit by a few
  batches' time, the gates (`before-commit.sh`, `level4.sh`), and the six
  runs again in a quiet block. It bounds a transaction's wait under
  pressure from any cause, not only a decrease.
* **(C) A gradual decrease** (010-P6, from Frans's words in this entry:
  "Gradual convergence to the new setting."). What: a decrease alone does
  not put the loads under pressure; the trigger goes down from the
  resident bytes to the new budget in steps no larger than the gap
  between the watermarks, one step after each of the eviction thread's
  batches, so that neither readers nor writers park for it. The
  convergence then takes about the time the batches need, as now. Larger
  than (B): a schedule in `Eviction` and its interleavings with
  `setBudget` (005-80's race), tests, `level4.sh`. It does not bound a
  transaction's wait when loads outrun eviction.

Recommended: (B), as it bounds the wait where it arises and is small;
then the six runs again in a quiet block, which also settles waits 3 and
4 and the spread of (a).


Decision, 2026-11-04
--------------------

Frans, 2026-11-04, 18:51: "52, do as recommend, Option B." So (B) of the
proposal in Results, 2026-11-04 night: the writer's warmup does not wait for
eviction; then the six runs again in a quiet block.


Option B, done
--------------

2026-11-04, by Claude (Opus 5.5, Claude Code), in a clone of `main`; the code
is one commit, `8defe65` (on `2dae7e5`).

* **The mechanism.** `Eviction.afterLoad(Db, boolean paced)`: a load that
  finds the resident bytes over the trigger wakes the eviction thread, as
  before; under pressure (over the trigger by more than the gap between the
  watermarks) only a paced load waits for the thread's next batch, at most
  `LOAD_WAIT_NANOS`, 2 ms. A reader's load is paced (009-02, step 3d); a load
  of a transaction's warmup (`Db.warmup`) is not: it wakes the thread and
  goes on. A load under the write lock neither waits nor wakes, as before.
* **How a warmup's load is told from a reader's.** The load listener gets
  the follow's `OpData`: `NodeCollection.LoadListener.loaded(OpData op)`,
  called by `NodeCollection.followPointer` after a read from the stream, as
  before. The warmup's `GetData` has a class of its own,
  `Trans.WarmupGetData` (package-private; `Trans.Builder` makes it, the only
  maker of `t.warmupGetData`), and `Db`'s listener calls
  `eviction.afterLoad(Db.this, !(op instanceof Trans.WarmupGetData))`. The
  cost on the read path: an argument and a type check, only after a read
  from the stream; a follow that finds its object in memory makes no call,
  as before. The comments in `Db`'s constructor, `Trans`, `NodeCollection`
  and `Eviction` cite bergdb 005-52.
* **A counter**, `Eviction.loadWaits` (an `AtomicLong`, incremented only by a
  load that then waits; a package-private getter), for the tests.
* **Unchanged:** the readers' pace; the batches, their bounds and the
  trigger; `setBudget` and the trigger's write under the monitor (005-80:
  `Eviction.testSetBudgetAtBatchEnd` passes); the stream's bytes
  (EvictionInvariance in `level4.sh`); `Db`'s public methods.

**The statements that changed.** No documented bound on the resident bytes
was a hard one: the budget is what the batches converge to, and pinned
state may exceed it. What changed is who waits, and so how far the resident
bytes may rise above the readers' pace:

* docs/levels.md, section 7, the capacity controller: "A reader's load that
  finds the resident bytes far over the trigger waits up to 2 ms for that
  thread. A transaction's own reads of its keys before the write lock
  (`Db.warmup`) wake it and do not wait (005-52), so the resident bytes may
  rise by what they load (the paths of the keys and their present values)
  until the transaction's end runs a batch." Before: "A load that finds
  the resident bytes far over the trigger waits up to 2 ms for that
  thread."
* `Database.setCacheSizeInMb`: "reads may wait for a batch meanwhile, at
  most 2 ms each" stays, and: "A commit's own reads of the keys it writes
  do not wait, and the commit runs one batch at its end (bergdb 005-52); the
  memory held may rise by what those reads load until then."
* `Eviction.afterLoad`'s Javadoc and the wake protocol's item 4 (`wake`).

**What one warmup may add, a correction of the proposal.** The proposal
said the rise is "bounded by the transaction's size (`checkSize`)". That is
not exact. The warmup reads the index paths of the transaction's keys and
the keys' present values, not the transaction's new ones, and it reads with
`Dag.CACHE_ALL`, so a present value over 1 MiB is kept too (a reader's
`CACHE_ALL_EXCEPT_LARGE_VALUE_NODES` does not keep one). `checkSize` bounds
the transaction's new values and keys, not these bytes; the present values
were written by earlier transactions. And several writers may be in their
warmups at once, outside the write lock. So the rise is bounded by the
index paths and present values of the keys of the warmups in progress,
summed over them, until each transaction's end runs a batch. B changes
what a warmup loads in nothing, only that it no longer waits between its
loads; the thread, woken by the first, runs meanwhile.

**The Lean model and the alignment.** Nothing to change. Concurrency is
outside the model, and 009-05's R3 says that "the bytes, the CLOCK bit, the
trigger and the thread are not in the model"; no invariant (INV-CAN, the
pins, INV-SLOT, the handles') is about when a load returns, and B changes
nothing that is evicted or written.

**The test**, `CapacityTester.testWarmupDoesNotWait` (unit, about 0.09 s):
3,000 keys of 300 bytes, started cold with a budget of 10 MB, k0 to k999
read. With the write lock held by the test (the eviction thread cannot run
a batch, so the pressure stays and no wait ends early): the budget lowered
to a quarter of the resident bytes, under pressure; a writer's transaction
of 1,000 puts to k1000 to k1999, whose values are not resident: its warmup
loads at least 1,000 times, none of its loads waits (`loadWaits`), and the
writer goes on to wait for the write lock (`Db.Internal.writersWaiting`).
A reader then gets k2000 to k2019, not resident either: at least 20 of its
loads wait. With the lock let go, the transaction commits, its values are
read back, and its end ran a batch (`afterTransaction`). Counts, not times:
no bound on the wall clock, so that a busy machine does not fail it; the
runs below time it. Mutations, in a copy: every load paced (B undone): "the
warmup's loads that waited, expected 0, got 1281" (2.7 s, a wait of 2 ms
for each); no load paced: "the reader's loads that waited: 0".

**The gates**, on the tree committed: `java/` and `lean/` of `9b67a82` (005-47)
with the change, the same as at `2dae7e5`, the commit's parent, which
changed only documents.

* `java/before-commit.sh`, 2026-11-04, 19:11 to 19:13: `BEFORE COMMIT OK
  (104 s)`, 1,134 unit tests and 81 f-tests. Before, on `bd77904`: 1,128
  and 79, also OK.
* `java/stress/level4.sh`, full, 19:13 to 19:27: `LEVEL 4 OK`.
  EvictionInvariance 9 of 9; RestartInvariance, CrashTest and ReclaimStress
  with the schedules every and random, the audit on; ReclaimReaders 5 of 5;
  the conformance with the Lean model with eviction (45 traces `TRACECHECK
  OK`; C-P and C-H, 0 of 10,344 transactions fail); LargerThanMemory (50 MB
  resident at a budget of 50 MB).
* Also, `java/night.sh` on `8defe65`, 2026-11-05 at 02:10: `NIGHT OK (39
  minutes)`: before-commit, the core build, Levels 1 to 4, the night tests
  and the medium conformance, each ok (`java/build/night/2026-11-05-0210/`,
  `report.txt`).


Results, 2026-11-04 evening
---------------------------

The six runs again, by Claude (Opus 5.5, Claude Code), on the jar of
`8defe65` (SHA-256 `7b80b9f9`), JDK 27, by the step's script with its runs
as they were (2 GB heap, 1M keys of 100 bytes, 4 readers, 60 s a phase; (a)
a fixed budget of 100 MB; (b) 400 MB, lowered to 100 MB 10 s into each
phase; ZGC a1, b, a2, then G1 a1, b, a2).

**On s1, not F53.** F53 did not get quiet: a wrapper waited 45 minutes,
19:28 to 20:13, for a 1-minute load of at most 1.3 and no gate, perf or
stress run, and gave up ("NOT QUIET after 2700 s"). The load stayed at
about 3.2, most of it macOS's `mediaanalysisd` at about 80 percent of a
CPU; no gate ran. s1 was quiet (load 0.12, no JVM; 005-47's measurement
there had ended, `ec58389`), so all six ran there, 20:14 to 20:27: `lowered:
OK, 0 problems`, six runs `PAUSE PROBE OK`, two lowerings in each (b), 12 of
12 rows; nothing but the probe's JVM used over 20 percent of a CPU meanwhile
(sampled every 30 s). s1 has two virtual CPUs (x86) and 3.8 GB: the 4
readers, the writer, the eviction thread and the collector share two CPUs,
so these times are not comparable with F53's table in Results, 2026-11-04
night; only (b) against (a) on s1 is. The step's copy for s1 changes the
JDK's path, drops `caffeinate` and reads the load from `/proc/loadavg`.

The outputs, outside the repository, in
`/Users/f/fl/bench/016/005-52/run-2026-11-04-B/`: `out/` (each run's text
and GC log, `runs.txt`, `summary.txt`), `load.txt` (s1's load during the
runs), `quiet.txt` (F53's wait), `jar.txt`; beside it the scripts
`prep-B.sh`, `quiet-run-B.sh` and `s1-B/night/`.

Per run and phase; times in ms. Batch: the longest eviction batch so far in
the run. Reached: seconds from the lowering to the resident bytes at most
100 MB. A p99.9 is the lower bound of the probe's bucket (a quarter of a
power of two).

| Run | Phase | Gets | Gets p99.9 | Gets max | Commits | Commits p99.9 | Commits max | Batch | Reached |
|---|---|---|---|---|---|---|---|---|---|
| zgc-a1 | tsize=1    | 11,044,450 | 3.67 |   57.87 | 410,733 |  10.49 |   51.69 |  23.59 | -           |
| zgc-a1 | tsize=1000 |  7,110,336 | 5.24 |   19.12 |   1,513 |  83.89 |   97.33 |  23.59 | -           |
| zgc-b  | tsize=1    | 11,700,551 | 3.67 |  354.57 | 423,475 |  10.49 |  395.54 |  15.18 | 0.604       |
| zgc-b  | tsize=1000 |  7,853,375 | 4.19 |   27.56 |   1,607 |  67.11 |   84.59 |  17.63 | not reached |
| zgc-a2 | tsize=1    |  9,733,500 | 3.67 | 1042.58 | 397,352 |  10.49 | 1036.90 |  12.04 | -           |
| zgc-a2 | tsize=1000 |  7,057,664 | 5.24 |   20.66 |   1,616 |  83.89 |   89.45 |  15.41 | -           |
| g1-a1  | tsize=1    | 11,089,840 | 3.67 |  114.10 | 618,804 |   8.39 |  109.23 | 105.00 | -           |
| g1-a1  | tsize=1000 |  9,620,165 | 3.67 |  126.95 |   1,461 | 134.22 |  170.84 | 128.78 | -           |
| g1-b   | tsize=1    | 11,920,005 | 3.67 |  115.29 | 666,070 |   8.39 |  115.15 | 111.42 | 0.336       |
| g1-b   | tsize=1000 | 10,056,525 | 3.67 |  423.87 |   1,509 | 234.88 |  704.60 | 125.12 | not reached |
| g1-a2  | tsize=1    | 10,307,639 | 3.67 |  122.12 | 592,030 |   8.39 |  120.78 | 120.74 | -           |
| g1-a2  | tsize=1000 | 10,110,983 | 3.67 |  127.86 |   1,477 | 134.22 |  174.72 | 120.74 | -           |

In the phase tsize=1000 the resident bytes stayed above 100 MB with the
fixed budget too, 127 to 132 MB at the phase's end, so "not reached" in (b)
(130 and 133 MB) is the phase's state on s1, not the lowering's.

**(b) against (a).** The longest waits, by `sum52.py`'s rule (LONGER: above
the larger of a1 and a2 by more than their spread, |a1 - a2|), with (b)'s
uptime, before or after its phase's lowering (zgc-b at 22.130 and 82.178 s,
g1-b at 20.295 and 80.321 s), and the cause in its GC log:

| GC | Phase | Longest | a1 | a2 | b | Spread | Verdict | (b)'s: uptime, s; cause |
|---|---|---|---|---|---|---|---|---|
| ZGC | tsize=1    | get    |  57.87 | 1042.58 | 354.57 | 984.71 | ok     | 17.665, before: a ZGC stall   |
| ZGC | tsize=1    | commit |  51.69 | 1036.90 | 395.54 | 985.21 | ok     | 17.696, before: the stall     |
| ZGC | tsize=1000 | get    |  19.12 |   20.66 |  27.56 |   1.54 | LONGER | 78.705, before: no GC event   |
| ZGC | tsize=1000 | commit |  97.33 |   89.45 |  84.59 |   7.87 | ok     | 92.092, after                 |
| G1  | tsize=1    | get    | 114.10 |  122.12 | 115.29 |   8.02 | ok     | 26.302, after: a young pause  |
| G1  | tsize=1    | commit | 109.23 |  120.78 | 115.15 |  11.55 | ok     | 26.302, after: the pause      |
| G1  | tsize=1000 | get    | 126.95 |  127.86 | 423.87 |   0.91 | LONGER | 77.323, before: a Full GC     |
| G1  | tsize=1000 | commit | 170.84 |  174.72 | 704.60 |   3.88 | LONGER | 77.336, before: the full heap |

Of the p99.9s, one is LONGER: G1's commits with 1,000 puts, 234.88 against
134.22 ms. With 1,509 commits it is about the second longest: the waits of
213 to 254 ms that end at 73.405 to 73.434 s, before the lowering (a G1
pause, below).

The causes, from the GC logs:

1. **G1, tsize=1000, before the lowering: the heap ran out.** At 73.194 to
   73.405 s a young pause of 210.5 ms with an evacuation failure (1,869 to
   820 MB); the waits of 213 to 254 ms end there. At 76.649 to 77.320 s a
   young pause of 246.8 ms with an evacuation failure (1,888 to 2,046 MB of
   2,048), another of 82.8 ms, and a Full GC of 337.1 ms (2,047 to 254 MB),
   one safepoint of 420.6 ms: the gets of 420 to 424 ms end at 77.320 to
   77.323 s, and the commit of 704.6 ms, from 76.631 s, spans the three
   pauses. (a)'s G1 runs had neither: no Full GC, no evacuation failure,
   the longest pause 123.3 ms (a1) and 118.5 ms (a2); after g1-b's lowering
   its longest pause is 116.1 ms. So (b)'s budget of 400 MB, before it was
   lowered, left G1 too little of a 2 GB heap on two CPUs: the collector's
   waits, not BergDB's, and not the decrease's.
2. **ZGC, tsize=1, before the lowering: allocation stalls.** Stalls of 352
   to 366 ms in every thread at 17.665 to 17.669 s, 4.5 s before the
   lowering: the get of 354.6 ms and the commit of 395.5 ms. (a) has them
   too: zgc-a2 a stall of 1,042.5 ms at 49.9 s (its get of 1,042.6 ms and
   commit of 1,036.9 ms), so (a)'s spread is 985 ms; zgc-a1 none, and zgc-b
   none after a lowering. ZGC's stalls on two CPUs, not BergDB's.
3. **ZGC, tsize=1000, a get of 27.56 ms before the lowering** (78.705 s,
   3.5 s before it), 6.9 ms above (a)'s 20.66 ms: no pause or stall near it
   (a pause of 0.019 ms at 78.463 s). Most likely the scheduling of the
   probe's threads and the collector's on two CPUs.

After the lowerings no wait of (b) is longer than (a)'s maximum. Under ZGC
the longest commits after them are 84.6 ms with 1,000 puts ((a) 89.5 and
97.3 ms) and at most 34.3 ms with one put; under G1, waits of at most
115.3 ms with one put, at young pauses of 104 to 111 ms ((a)'s longest
waits 109 to 122 ms), and commits of at most 169.8 ms with 1,000 puts ((a)
170.8 and 174.7 ms). The first
transaction after each lowering, which the writer starts at once, is not
among the five longest commits of its phase; on 2026-11-04 night it was the
longest (194.9 ms under ZGC, 96.8 ms under G1).

**The verdict.** As written, Left to do's rule ("no wait in (b) is longer
than in (a) beyond the spread between two runs of (a)") has four LONGER
verdicts, so it is not met to the letter. The coordinator's reading
(2026-11-05), recorded as such, so that Frans can reopen the entry if he
reads the rule otherwise: the point reopened was the decrease's own wait,
and it is gone. No wait from the lowering on is longer than (a)'s maximum,
and the first large transaction after a decrease no longer waits for the
convergence. All four LONGER verdicts come before the lowering, while (b)
ran at 400 MB, on a machine of two CPUs whose (a) runs were noisy
themselves (1,042 ms in zgc-a2); three are the collector's (G1's
evacuation failures and Full GC, ZGC's stalls), one (27.6 ms) the
machine's. So the point is met, and the entry is done.

For release 2026.2 (016-05): the point is met on `main` by B, `8defe65`.
The release's commit, `c459883`, came before B, so 2026.2 keeps the wait of
Results, 2026-11-04 night: a large transaction right after a decrease may
wait about as long as the convergence.


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
`4d74c19`.

2026-11-03, 16:49 to 16:52, by F1, steps 7 and 8:

* **The prep** (step 7), by `/Users/f/fl/bench/016/005-52/prep.sh` (a
  fresh clone of `main`, as the work clone keeps its entry edits): `main`
  at `17270d1` (the probe's commit `4d74c19` and one of documents), `sh
  java/build.sh`; `bergdb.jar` and `stress/` copied to `$R`; `$R/jar.txt`:
  `17270d1ca38e184947a332ab61f4bb097c66963d` and the jar's SHA-256
  `665ef9ceeeb826caef74c486970e2437953bfadd7cb5904c0f25dd623eba7ed6`.
* **READY** (step 8): `SMOKE=1 sh night/lowered.sh`, from the main tree's
  path, 16:50:41 to 16:51:30 (F53 loaded, about 50): six runs OK, 2
  lowerings in each (b), the summary complete (12 rows); its last line
  `lowered (SMOKE): OK, 0 problems;
  /Users/f/fl/bench/016/005-52/run/smoke/summary.txt`. Then `touch
  night/lowered.sh.READY` (16:51).

2026-11-04. Steps 9 and 10. The conductor's step `52-lowered` ran 03:43 to
03:56 in night 1's window 2, NOT QUIET (it waited 30 minutes for quiet
after 005-65's step; load 2.52 at the start), exit 0, `lowered: OK, 0
problems`. Written up in Results, 2026-11-04 night: four LONGER verdicts;
two are the decrease's, the first commit of 1,000 puts after the lowering
waiting about as long as the convergence (194.9 ms under ZGC, 96.8 ms
under G1, against at most 40.6 and 37.2 ms with a fixed budget), most
likely through its warmup's loads, each parked up to 2 ms for a batch;
the other two came before the lowering (a stall of about 11 ms under ZGC,
a G1 pause). Not met: a stop for Frans, with options (A) to (C) and (B)
recommended. The raw outputs stay in `/Users/f/fl/bench/016/005-52/run/out/`;
the markers removed.

2026-11-04 and 05. Option B, decided by Frans at 18:51, done by Claude
(Opus 5.5, Claude Code) in `8defe65`: a transaction's warmup no longer
waits for eviction; `CapacityTester.testWarmupDoesNotWait`;
`before-commit.sh` and `level4.sh` OK, and `night.sh` OK on it (2026-11-05,
02:10). The six runs again, 2026-11-04, 20:14 to 20:27, on s1 (F53 not
quiet for 45 minutes): no wait after a lowering longer than (a)'s; four
LONGER verdicts, all before the lowerings, the collector's and the
machine's. Closed 2026-11-05 on the coordinator's reading of the rule
(Results, 2026-11-04 evening).
