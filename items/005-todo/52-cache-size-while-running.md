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
