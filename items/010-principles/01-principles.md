Created 2026-10-26 by Frans Lundberg



010-principles
====================

The principles of BergDB.



List of principles
====================

Numbered principles. A principle is followed where possible; if we must,
we break it, and each deviation is documented here, under its principle
(Frans, 2026-10-26: "If we must, we can break principles. Deviations should
be documented in 01.").


P1. No stop-the-world
---------------------

Worst-case behaviour counts. No get or commit waits a long time because
BergDB, or the collector, does work for the whole database at once. The
target is a worst case of about 20 ms.
The measure is the longest pause, not the mean or a percentile.

Readers too (010-02's candidate 2, merged here on 2026-10-26): no
stop-the-world for readers. A reader may wait a short time to take a lock,
but never long. Frans: "What is really meant is that we should not have
stop-the-world for readers. We may have short "blocks" when a reader
aquires a lock. But it should be short." The old texts promised more: "Read
transactions will NEVER block!" (2008-08-06); "Readers are never blocked by
writers or other readers." (BergDB features, 2013-08). Frans thinks this
can be achieved, and wants to look at it more.

Where BergDB stands:

* Readers never take the write lock (009, step 3b). A reader that loads a
  node takes the handle's monitor (009, T7a), and, when the cache is over
  its budget, waits for the eviction thread's batch at most 2 ms
  (`Eviction.LOAD_WAIT_NANOS`): short waits, as P1 allows.
* A read of the stream's last file waits for the writer's append and its
  force, one monitor for both: seconds on s1's disk, the longest waits left
  for readers with handles
  ([005-46](../005-todo/46-stream-file-lock.md), 009-03). A deviation.
* To look at (Frans, 2026-10-26): every place where a reader can wait
  today, and for how long.
* Eviction: the sweep that walked the resident set under the write lock,
  up to 266 s in 004-02, is replaced by handles and bounded steps (item
  009, on `main` since 2026-10-26).
* The collector: only ZGC and generational Shenandoah meet the target; G1
  does not ([004-04](../004-indirect-swizzling/04-zgc.md)), and
  generational Shenandoah stopped for 182 and 821 ms in the soak with
  eviction ([009-04](../009-handles/04-shenandoah-degenerated.md)).
* The deadline of 007-03 makes one long commit, while the other writers
  and the readers of the stream's last file wait
  ([007-04](../007-bounds/04-review-after-009.md), points 6 and 7).


P2. A deterministic stream
--------------------------

The bytes of the stream are a function of the transactions, their contents
and their order, and nothing else: not of timing, threads, restarts or the
state of the cache. Frans's goal of 2015-12-28: "a restart can be inserted
between any two transactions without affecting the bytes in the stream".

The transactions are deterministic too: "Is a KissDB transaction always
deterministic? Answer: Yes." (2008-08-02). So a transaction needs no
rollback: what may refuse it is checked before it changes anything (the go
point; [levels.md](../011-docs-archive/04-levels.md), "A transaction or a read that
fails"). A failure after that point is P7's.

Where BergDB stands:

* Proved for the abstract records: T2, restart invariance
  ([sis-model.md](../../docs/sis-model.md), section 9), on assumption A1,
  determinism of the transactions.
* Checked for the bytes: the restart checks require byte equality
  (`RestartInvariance`, [levels.md](../011-docs-archive/04-levels.md)); the padding
  bytes that the 2017 code left uninitialized were fixed on 2026-10-12.
* To check: that the memory budget and eviction (Level 4, item 009), the
  buffer time and the startup distance's deadline (007-03) leave the bytes
  unchanged, or, where a setting changes the bytes, that the principle says
  so.


P3. Calm when not used
----------------------

BergDB consumes resources when the application uses it, by calling methods
of the public API. That includes work that a call starts and that BergDB
finishes after the call returns, in a thread of its own: it is a response
to the application's call, temporary and limited, with no surprises. Such
work is allowed, whatever we call it (Frans, 2026-10-26: "We could call it
'background work', but it is in response to user calls. No surprises. No
matter what we call it, this is allowed."). What P3 rules out is work that
nothing in the application asked for. A database that is not used for some
time settles down: it consumes no resources besides memory, so no CPU, no
I/O, no wake-ups. Frans on 005-14: "I would like the database to be 'calm'
when not used. And consuming insignificant CPU resources."

Why (Frans, 2026-10-26):

* **BergDB is a library.** It runs in the application's process, so it
  shares the CPU, the memory and the I/O with the application. Work that
  BergDB starts on its own runs at a moment BergDB does not choose well:
  it does not know what the application is doing, or is about to do.
* **The application decides.** Only the application knows when it is
  idle. Maintenance at other times than the calls should be asked for by
  the application, visibly, not hidden inside BergDB.
* **Tests and determinism.** No sporadic actions: what BergDB does follows
  from the calls, so a run can be repeated and a test sees the same
  behaviour each time. This goes with P2.

A possible API, an idea for later (Frans, 2026-10-26): a call such as
`maintain()` that lets the application give BergDB time for maintenance,
controlled from the application's side. With it, running maintenance when
the application is idle is easy to add, by the application, which knows
when it is idle, or by a helper that the application chooses to use.

Where the work runs is free, within P1 and P4 (Frans, 2026-10-26, on
eviction): in the call that needs it, or in a thread of BergDB's own that
the calls trigger. "If run inside the calls, it must be fast enough to not
degrade performance substantially for the calls. In particular, P1 must be
followed. Worst case matters."

The work in threads of BergDB's own today, all fine as it is (Frans,
2026-10-26), with the call that starts it:

* A commit: `BufferedStream`'s consumer thread, one per stream, writes the
  buffer at the latest a buffer time (20 ms) after the commit, the
  durability promise of `sync(ORDINARY)` (005-13), and sleeps when nothing
  is buffered (005-14).
* A get or a commit that needs memory: the eviction thread,
  `bergdb-evictor`, one per database (009, decision T5a), is started or
  woken. A thread is fine (Frans, 2026-10-26). But when idle it waits with
  a timeout, `evictorLock.wait(1000)` in `Eviction.EvictorRun`, to see
  whether the database has stopped: one wake-up a second, as long as the
  database is open. A departure from "no wake-ups", registered as
  [005-51](../005-todo/51-eviction-on-calls.md): eviction only in response
  to the calls.
* Adding or deleting an index: a job in a thread of its own
  (`IndexBuilderImp.createInThread`, the `-delete-` thread of
  `DatabaseImp`).
* `stop()`: the buffered transactions are written in a background close;
  `close()` waits for it (005-35).
* A replica: its consumer thread. 005-14 recorded that it wakes twice a
  second; to check whether that still holds when it is idle.


P4. Maintenance proportional to the user's work
-----------------------------------------------

The maintenance that BergDB piggy-backs on the application's calls
(writing dirty index nodes, reclaim, eviction, the take of the startup
distance) is proportional to the size of the work the call asks for. No
surprises: no call that, now and then, costs far more than its size, in
time mostly, also in I/O and memory. Frans on 005-49 (2026-10-26): "I like
smooth operation. Good worst case behaviour. Bursts are to be avoided. In
general I like the cost of a user operation to be predicable and
proportionell to the size of the user-visible operation."

With P3, P4 is what keeps P1 for BergDB's own work: maintenance runs in
the calls, or as limited background work that a call starts, and each
call's share is bounded by its size, so no call stops for long.

Where BergDB stands:

* Index nodes are written in bursts at the startup distances a large
  database should use ([005-49](../005-todo/49-smooth-index-writes.md),
  from [005-38](../005-todo/38-writes-at-scale.md)).
* The deadline of 007-03 takes every transaction that is due, in one
  record, or a few at the record limit; after a decrease of the startup
  distance, that is one long commit (007-04, point 6).
* Eviction in bounded steps (009) is proportional by design; P1's
  measurements in 009-03 are its evidence.


P5. Bounded startup
-------------------

Startup takes a bounded time, whatever the size of the database and
however long it has run: the time does not grow with the data. "It is
important to be able to avoid reading the whole SS to startup the
database." (2008-08-23); "a short and constant startup time (O(1) in big O
notation). This is important as your data grows." (BergDB features,
2013-08); "The startup time of DB must be O(1), or at least not greater
than O(log(G.size()))." ([startup.md](../../docs/sources/startup.md),
2016-05-05).

Where BergDB stands, in item [007](../007-bounds/readme.md):

* T3 is proved in Lean: a startup pos policy that keeps up with the
  startup distance bounds the startup section.
* BergDB's own take does not keep up yet: 005-38 measured it past 2 × sd
  at 50 and 200 MB (007-04). The plan, 007-03, adds a deadline (D1), after
  smooth index writes (005-49). A deviation until then;
  [docs/levels.md](../../docs/levels.md), section 5, says so.
* A cold startup's random reads take minutes on s1 (007-04; 007-03, step
  6).


P6. No interruption for changes
-------------------------------

The database's setup changes while it runs, without stopping it or the
application's calls: indexes and replicas are added and removed, and
settings change. "This is great, we never want to take down the database!"
(2008-08-06); "Indexes can be added and removed with no locks and no
interruptions of ongoing operations." and "Replicas can be added and
removed while the database is running." (BergDB features, 2013-08). A large
change goes in steps, so that P1 and P4 hold while it runs: "it could make
sense to descrease startupDistance in steps of 1M and write a dummy
transaction after each change. This is to avoid a huge transaction with
dirty nodes." (2013-04-08; today 007-03's D4).

Where BergDB stands:

* Indexes: `Database.indexBuilder` and `deleteIndex` run as jobs while the
  database runs (P3's list).
* Replicas: `addReplica` and `removeReplica` while it runs; experimental,
  with known faults (005-11).
* The retain duration: `setRetainDuration` while it runs.
* The startup distance: set when the database is created. Through the Pub
  API, an existing database keeps the one in its stream
  (`DatabaseBuilder.startupDistanceInMb`); the core can change it while the
  database runs (`Db.setStartupDistance`), and 006-06 (fast restart)
  builds on that. A deviation. On-the-fly changes date from 2013-04, in the
  core and through JMX (`Jmx.DbMonitor`), never in the Pub API; the code is
  unchanged since. Being investigated in
  [005-53](../005-todo/53-startup-distance-on-the-fly.md).
* The cache size: set at start only (`cacheSizeInMb`); a change needs a
  restart. A deviation. It should change while the database runs, with no
  disruption: the cache converges gradually to the new size (Frans,
  2026-10-26: "Gradual convergence to the new setting."). Registered as
  [005-52](../005-todo/52-cache-size-while-running.md); the core can do it
  already (`Eviction.setBudget`, also through JMX).
* Fixed for the life of the database, by decision: the crypto key. The log
  of 2008-10-18, `doc/log-old/2008-2011-log.txt` line 1253: "Discussion
  with Anton. Conclusion: do NOT ever change encryption key of stream. This
  CAN be done while the database is running, but it complicates for
  administrator of the database. The real security may actually be lower
  because of increased risk of administration mistakes." The day before,
  the log had considered key names, to allow a change while the database
  runs.


P7. A failed database stops
---------------------------

A database whose environment has failed (an I/O error, corrupt data), or
that has a bug, does not run on. It fails: the call throws, and so does
every later transaction and read, until the application stops the
database and starts it again. "We do not want the application to run if
its environment (needed assumptions) is faulty or if there is a bug."
(2013-01); "FatalDBException - an error happened in the database that
makes it unusable. Usually handled by logging the error and stopping the
database." (2012-08). A refused transaction is another matter: it changes
nothing, and the database goes on (P2).

Where BergDB stands: as P7 says, since 005-01 for transactions and 005-30
for reads and syncs (`DbFailedException`; [levels.md](../011-docs-archive/04-levels.md),
"A transaction or a read that fails").


P8. Determinism beyond the stream
---------------------------------

Where possible, BergDB does the same in each run of the same calls, not
only in the stream's bytes (P2): what it keeps in memory, what it evicts,
the work it does and when. Nothing depends on the JVM's memory or on
timing, where that can be avoided. "It is non-deterministic which defies
the philosophy of BergDB. For testability etc, we want perfect
determinism. We also want a cache that keeps track of exact sizes."
(2017-07-30); "Note that if we wrap INode in a SoftReference, we loose our
deterministic approach. JVM will evict, no full control." (2015-01-03).

Where BergDB stands:

* The cache counts its bytes exactly (`Residents`), its budget is a number
  of bytes, and it uses no weak or soft references (`Cache3`, 2017: "A
  deterministic node cache; size is known, weak references are *not*
  used."). The default budget is a fifth of the JVM's maximum heap, fixed
  for a run.
* The eviction schedules for tests are deterministic: none, values, every,
  and random with a seed.
* The default schedule, the budget, is not: a batch ends after 2 ms
  (`Eviction.BATCH_NANOS`) or when a writer waits, and the eviction thread
  runs when readers' loads wake it (009, step 3d). What is resident, and
  so what a later get must load, depends on timing and on the threads. A
  deviation, made for P1.


P9. No global state
-------------------

BergDB keeps no global state. An application can run several BergDB
databases in the same JVM process, and they do not affect each other.
BergDB is controlled through code. The `bergdb.dev` package doc, by
2013-06-06 and still in `java/src-dev/bergdb/dev/package.html`: "Do not
use JVM global stuff (non-final "static" fields). It should be possible to
run multiple BergDB instances in one JVM. Easy testing, limited
dependencies. BergDB should run well in the same JVM together with other
software." BergDB features (2013-08): "There is no use of global logging,
environment variables, command line arguments, files with settings. BergDB
is controlled completely through ordinary code. Multiple instances of
BergDB can run in the same process without problems."

Not part of P9 (Frans, 2026-10-26): in the 2012 era, BergDB of different
releases could run in the same JVM, useful for tests that write with one
release and open with another.

Where BergDB stands (`java/src`, 2026-10-26):

* Non-final static fields: test hooks (`Db.testHooks`,
  `NodeCollection.firstTouchListener`, `DatabaseImp.testHookAfterStart`),
  a test knob (`StoredTrans.recordLimit`, set by `DbTester`), counters for
  the whole process (`Eviction.allUnswizzled` and `allReleased`, those of
  `Audit`), and facts about the JVM, found once (`Util`, `IcuInfo`).
* System properties set defaults, for tests and stress programs: `evict`,
  `evictseed` and `evictbudget` (the eviction schedule), and `audit`.
  `Audit` prints to `System.err` when an audit fails.
* To check: whether any of these lets one database affect another in the
  same JVM.


P10. No administration, few settings
------------------------------------

BergDB needs no administration. It has few settings, and the defaults
work: there is no need to tune settings for good performance. "Self-tuning",
"No db administration", "Sensible defaults" (2008-08-02); "Zero database
administration. Database administration is never needed and there are few
settings. There is no need to spend time optimizing settings to reach high
performance; most often, the default settings are fine." (BergDB features,
2013-08). Of settings that are constant for the life of the database:
"These constants should be avoided whenever possible." (2013-01).

Where BergDB stands:

* The Pub API's settings (`DatabaseBuilder`): the directory, or memory;
  the crypto key; the clock; the retain duration; the startup distance
  (default 50 MB, clamped to 5 to 1000 MB); the cache size (default a fifth
  of the JVM's maximum heap).
* The default startup distance does not suit a large database: from about
  10M keys, 200 to 1000 MB does (005-38), chosen when the database is
  created (P6). A deviation. 2013-04-08: "It is not clear to me how to do
  automatic startupDistance changes based on db size."
* The node size is not a setting of the Pub API (30). Through the core, a
  database started with another node size than it was written with fails,
  with an error that looks like a corrupt stream (005-50).


P11. Simple before optimal
--------------------------

Simple, correct code comes before the last bit of speed. Frans
(2026-10-26): "We want it fast, but not at any complexity price." The old
texts: "As simple as possible. Prioritize easy-to-read code over
performance." (2012-01-03); "FIGHT COMPLEXITY AND UGLY CODE! And keep
dev.CorePerf ok." (2014-01-24). They named a price: "I would trade to 1.50
for bug-free, easy-to-maintain and understand code." (2013-09); "A < 2.0
factor performance degradation compared to now is OK if we can achieve
this." (2015, fourth quarter).

A principle for decisions on the design and the code, not on BergDB's
behaviour; it has no measure of its own today.


P12. A small Core Layer
-----------------------

The Core Layer has a small API, and we keep it small. The API is Db's
public methods; dag, storage and stream are under them. What can be built
on top of the Core API is built on top, not added to it. Frans
(2026-10-26): "I think the principle is to maintain the small core layer.
Avoid adding more to the layer's API. Better to implement on top."

All data passes through four methods, the Core Data API: `getOne`,
`getMany`, `getTrans` and `execute`. The rest of the Core API runs the
database or reports on it, and reads or writes no data: the lifecycle
(`start`, `stop`, `close`), `sync`, settings and status.

The Core Layer does not depend on the layers above: its packages never
import `pub` or `pubimp` (`pub.util` is shared with lower layers). Each
package's `package.html` lists its allowed dependencies.

From the Db Javadoc, in the first commit of the 2013 repo (2013-06-06),
with `get()`, `getMany()` and `execute(Transaction)`: "This API form a
narrow "waist" with a large code base under it and potentially a large
code base "above" it. These methods are believed to be "feature complete"
in the sense that all features we want from the database can be
implemented on top of them. Functionality that can be provided by using
only the Core Layer API, should not offered by this class." `getTrans` came
on 2016-03-30, for `Connection.transactionInfo()`: the only widening of
the data methods.

Where BergDB stands (`java/src`, 2026-10-26):

* The Core Layer imports no upper layer: `core` imports `common`, `dag`,
  `nanotest`, `pub.util`, `storage` and `stream`. It builds alone, a
  program calls `Db` with only the Core Layer on its class path, and each
  of its seven packages imports only what its `package.html` allows
  (006-08, which moved `FileStreamPowerLossTester`, a tester that made
  `stream` import `core` and `storage`, to `core`).
* `pub` imports `core.SyncLevel` (in `Database`, `Connection` and
  `Transaction`): a core type in the public API. Its `package.html` says
  `pub.util` only.
* Stale `package.html` lists: `pubimp`'s leaves out `dag`, `storage` and
  `pub.util` (`core`'s and `dag`'s were fixed the same day; all of them in
  005-56).
* `getOneInternal` is public.
* Db has 43 public methods.

No measure today. Candidates: the number of Db's public methods, and
006-08's tools: each package's imports against its `package.html`
(`deps.py`), and the Core Layer built alone (`core-build.sh`).

