005-53 and 005-52: a setting changed while the database runs, the evidence
=========================================================================

By Claude (Opus 5.5, Claude Code), 2026-10-28, for 006-10's W4.2: a
reading of `main` at `b1111f4` (D4:B in the core since `f89846d`), and the
numbers of 007-06, 007-07 and 005-52's first step. No code changed, no run
made. The options are in full in the entries,
[005-53](../53-startup-distance-on-the-fly.md) and
[005-52](../52-cache-size-while-running.md); this is what they rest on.


1. Today's code
---------------

### 1.1 The Pub API

* `pub/Database`: the only setting it changes while running is the retain
  duration (`getRetainDuration`, `setRetainDuration`). Long work returns a
  `Job` (`deleteIndex`, `addReplica`; `IndexBuilder` too): `pub/util/Job`
  is "a long-running job performed in the background", with `getStatus`
  and `join`.
* `pub/DatabaseBuilder.startupDistanceInMb`: "Existing databases keep the
  startup distance stored in their stream." Its `@param` says "between 5
  and 100"; `pubimp/DatabaseBuilderImp.startupDistanceInMb` clamps to 5 to
  1000 MB (005-38 advises 200 to 1000 MB from 10M keys). The `@param` is
  out of date.
* `pub/DatabaseBuilder.cacheSizeInMb`: the budget of the cache, evicting
  down to three quarters of it; "What the database must keep in memory
  (the nodes changed since its startup position, of the order of the
  startup distance) is never evicted and may exceed it." Clamped to 4 to
  100,000 MB by `DatabaseBuilderImp.cacheSizeInMb`; the default, a fifth
  of the JVM's maximum heap and at least 2 MB, is set in the constructor
  and skips the clamp (a heap under 20 MB gives 2, where a call gives at
  least 4). A comment there: "we might want to clamp depending on
  startupDistance? 2 x startupDistance perhaps."
* `DatabaseBuilderImp.start` passes both to `DbBuilder` at every start;
  `DatabaseBuilderImp.retainDuration` passes the retain duration, whose
  core default is `Long.MAX_VALUE` (`DbBuilder`).

### 1.2 The core

* `core/Db.setStartupDistance(int)`: clamps to [2 × 200 kB, 1000 MB]; under
  the write lock sets the field, sets the in-memory meta block's value and
  commits a transaction with a 200 kB value under `DbConstants.DUMMY_KEY`
  (`RecoverableStream.META_BLOCK_DISTANCE`), so that a meta block in the
  stream holds the new value. Its Javadoc since `f89846d`: one call, no
  steps; the section comes down as transactions are committed. Two details
  for a Pub method:
  * The field and the meta block change before `execute` checks the state
    (`Db.assertDbStateIsActive`): on a stopping database the call changes
    the in-memory value and then throws `DbStoppingException`. No record
    follows, so nothing reaches the stream; untidy, not a fault.
  * A call with the value in force still writes the 200 kB transaction.
* `core/Db.getStartupDistance()`: the setting, under the write lock.
* Persistence: the startup distance is at offset 40 of every meta block
  (`storage/MetaBlock`), one every 200 kB of stream; `Db.handleStartParams`
  reads the last valid meta block's at every start, and a new database
  writes the builder's (`Db`, the first transaction). Tested by
  `DbTesterRestart.dbShouldRememberStartupDistance1` and `2`.
* Why it must be in the stream: it decides which index nodes each record
  takes (`TransSeq.take`, the share and the deadline), so a start must go
  on with the value in force for the bytes not to depend on restarts
  (010-P2). `DbTesterRestart.testSameStreamAfterDecreaseWithRestartsF`
  (007-07, 10.2): a decrease with a restart right after the call and every
  10 commits after gives the same stream, byte for byte.
* No overflow: `TransSeq.take` computes `2L * startupDistance` and
  `Reclaim.transactionCompleted` `2L * db.getStartupDistance()`, and the
  setting is at most 1000 MB, so 2 × sd is at most 2,000 MB (007-04's
  point 5, an overflow above 1,073 MB in `int`, does not arise).
* Reclaim follows a change at once since 005-61 (`transactionCompleted`
  reads `db.getStartupDistance()`).
* `core/Db.setRetainDuration(long)` sets `Reclaim`'s volatile field. Not in
  the stream: every start takes the builder's value. `Database`'s Javadoc
  does not say so. (An aside, not for these decisions: the retain duration
  shapes the stream's bytes, reclaim's rewrites and cuts, and yet a
  restart takes the builder's value; 010-P2's "To check" names the
  startup distance and the budget but not this.)
* The cache size: `Db`'s constructor gives it to
  `Cache3.setSizeIndicator` (clamped to at least 4 MB; read only by its
  getter, which the manual tool `Interactive` prints) and to `Eviction` as
  its budget. `core/Eviction.setBudget(long)`, synchronized, sets the high
  watermark, the low one (`LOW`, 3/4) and the trigger, all volatile. No
  method of `Db` reaches it: only `db.internal().eviction()`, which
  `Jmx.DbMonitor.setCacheSizeIndicator` uses, with `Cache3`'s.
* What a lower budget sets going: the next commit's batch (`Eviction`, at
  the end of a transaction, at most `BATCH_NANOS`, 2 ms) wakes the
  eviction thread if the resident bytes are over the trigger, and so does
  a reader's load (`Eviction.afterLoad`). While the resident bytes are
  over the trigger by more than the gap between the watermarks, a load
  waits for the thread's next batch, at most `LOAD_WAIT_NANOS`, 2 ms.
  With no calls nothing runs (005-51); `Eviction.wake` is private. Pinned
  state: a sweep sets `trigger = max(high, pinnedOfLastRound + (high -
  low))`, so a budget below the pinned bytes is not reached.
* The cache size changes no byte of the stream: `level4.sh`'s
  EvictionInvariance, "EVICTION INVARIANCE OK" on all 9 (007-07, 10.3).
* `core/Jmx.DbMonitor`: `get`/`setStartupDistance` and
  `get`/`setCacheSizeIndicator`; registered only by manual tools
  (`Huge`, `LoadA`, `TransThroughput`, `Interactive`; history.md, 5).
* `Db` has 43 public methods (010-01, P12).


2. The numbers
--------------

### 2.1 The startup distance, one call with D4:B (007-07, 10.4)

10M keys, F53, byte counts:

| decrease | `setStartupDistance`'s record | to 2 sd: puts, stream, largest record | after: section, largest record |
|---|---|---|---|
| 1000 to 100 MB, worst | 3.34 MB | 0.67M, 822 MB, 2.30 MB | 1.04 sd, 1.67 MB |
| 1000 to 100 MB, 20M | 3.61 MB | 0.59M, 817 MB, 2.94 MB | 1.05 sd, 1.54 MB |
| 200 to 50 MB, worst | 5.42 MB | 0.08M, 234 MB, 5.11 MB | 1.08 sd, 1.83 MB |
| 200 to 50 MB, 20M | 5.34 MB | 0.09M, 234 MB, 4.66 MB | 1.10 sd, 1.97 MB |

* Without D4:B, at the same points: one record of 486 MB and then 145 MB
  (1000 to 100), 87 and 72 MB (200 to 50) (007-06, via 007-07, 10.4).
  Caller's steps of 10 MB: records of up to 54 MB (007-06; Frans's
  decision 1 of 006-09).
* The section without its last record shrank at every record, below the
  new 2 sd after 81 to 86 records (200 to 50) and 587 to 669 (1000 to 100)
  (007-07, 10.4).
* Without writers nothing pays the debt (007-06, section 5, point 3). The
  stream needed is about 1.4 times the debt at the decrease.
* An increase, 1 to 4 MB (D4Probe): nothing becomes due, the section grew
  to 1.02 times the new setting, the records were smaller on average
  (1,203 bytes against 1,326) (007-07, 10.1).
* The 200 kB value counts as own bytes and earns the record its share:
  3.3 to 5.4 MB at 10M keys; at 200 to 50 MB about 9 commits of 4.4 to 5.1
  MB follow. Not counted (a prototype): 0.2 MB, but the section came down
  later, 370 commits instead of 73 for 8 to 1 MB (007-07, 10.5; open for
  Frans there).

What a setting is worth, steady state, updates at 10M keys: 867, 524 and
190 stream bytes a put at 50, 200 and 1000 MB (007-07, 10.4; 007-06,
section 4). A cold start at 10M keys on s1: about 46 s at 50 MB and 51 s
at 200 MB (005-57).

### 2.2 The cache size (005-52, the first step)

F53, 10M keys, jar `a6cd234`, `setBudget` from 664 MB resident:

| run | new budget | reached after | eviction thread's CPU | longest batch | longest get | longest commit |
|---|---|---|---|---|---|---|
| ZGC, to a fifth | 132 MB | 47.0 s | 22.0 s | 2.18 ms | 6.09 ms | 38.4 ms |
| G1, to a fifth | 132 MB | 46.9 s | 26.3 s | 88.8 ms | 36.7 ms | 45.1 ms |
| ZGC, to a half | 332 MB | 0.31 s | 0.19 s | 2.22 ms | 4.12 ms | 28.5 ms |

The budget converges in bounded batches under ZGC; G1's 88.8 ms is most
likely a collection inside a batch. The commits are not yet compared with
a fixed budget's (005-52's "Done when").


3. The options against today's code
-----------------------------------

005-53's options are those of history.md's last section, written before
D4:B.

| option | after D4:B |
|---|---|
| A, keep the deviation | still valid; no work, P6 stays broken |
| B, a setter returning a `Job` | obsolete as written: its job was to run D4's steps, which the take now does after one call; what is left is a job that does no work, finished by the application's commits, and never on an idle database (2.1) |
| C, the builder's value for an existing database | subsumed by E: one line after `start()` does it, explicitly, and the builder's promise stays |
| D, B now and C later | falls with B |
| E, new: a plain setter and getter, kept in the stream | what D4:B makes possible: the call returns when the setting is in the stream |

005-52's questions 1 and 3 give three forms: A (JMX only, as now), B (a
setter and a getter for the run) and C (B, kept in the stream).


4. One pattern for "change a setting while running"
---------------------------------------------------

| setting | changes the stream's bytes | kept in the stream | what converges after a change | driven by |
|---|---|---|---|---|
| startup distance | yes, the take (`TransSeq.take`) | yes, every meta block (`MetaBlock`, offset 40) | the section, to about the setting | commits (D4:B) |
| cache size | no (EvictionInvariance) | no | the resident bytes, to the budget | commits and loads, batches of 2 ms (005-51, 005-52) |
| retain duration (today) | yes, reclaim | no | the first available lookup time | commits (`Reclaim.transactionCompleted`) |

The pattern the entries recommend: `Database.setXInMb(int)` and
`getXInMb()`; the setter returns when the setting is in force (for the
startup distance: in the stream); it clamps as the builder does; the
getter gives the setting, the target, not the state that converges to it;
the convergence is the database's ordinary work, started by the calls, in
bounded pieces (P1, P3, P4); no `Job`, which is for work that runs in the
background and ends. The rule for persistence: a setting that shapes the
stream's bytes is kept in the stream (P2), one that does not is for the
run. Each setter's Javadoc says which, and `setRetainDuration`'s should
too.


5. 005-53's other questions
---------------------------

* Question 1, the decrease measured: 007-06 and 007-07 (2.1). With D4:B
  no step size is needed: one call, records of at most 5.4 MB at 10M keys.
  The 20 ms of 010-P1 for a record of 3 to 5 MB was not timed; such
  records are within 3 times the steady runs' largest (0.23 to 1.93 MB).
* Question 3: answered, fixed in 005-61.
* Question 4: T3 holds for the deadline in force, max(2 sd, span) (007-07,
  10.1; the Lean form is 007-03's step 4). No overflow (1.2). A change of
  the distance changes the bytes through a transaction in the stream, so
  P2 holds as for any transaction (the restart test, 1.2); P2's "To check"
  in 010-01 can say so.
* Question 5: section 4.
