Created 2026-10-26 by Frans Lundberg



010-principles
====================

The principles of BergDB.



List of principles
====================

Numbered principles. They guide the development: mostly they are
followed, and where one is not, the exception is justified and documented
here, under its principle (Frans, 2026-10-26: "If we must, we can break
principles. Deviations should be documented in 01."). A few simple
principles will always need exceptions (Frans, 2026-10-27: "That is the
thing with principles. They should guide, but a few simple principles will
always need exceptions.").


P1. No stop-the-world
---------------------

Worst-case behaviour counts. No get or commit waits a long time because
BergDB, or the collector, does work for the whole database at once. The
target is a worst case of about 20 ms.
The measure is the longest pause, not the mean or a percentile.

The target is a guide, not a hard limit (Frans, 2026-11-06, 12:28, on
019-36): "20 ms is just a target for a fast server. I see it more like: a
wait at 20 ms or more is interesting to have a look at. May be worth
fixing. We don't expect to remove all such cases. A loaded machine, slow
network-based storage, small VPS." For a wait such as 019-36's, under
50 ms on F53 is good and under 20 ms great, under 100 ms on s1 good: "It
is a trade-off. Between complexity, time to fix, other performance
figures, maintenance cost etc."

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
  (`Eviction.LOAD_WAIT_NANOS`): short waits, as P1 allows. Since
  2026-10-29 a load enters the eviction thread's monitor, `evictorLock`,
  only when no request to the thread is pending, and no longer on every
  load over the budget: with 8 readers from the OS's cache at 665 MB under
  ZGC on F53, 78,000 loads a second entered it, and its queue made
  after-load calls of over 10 ms, a fifth of the gets over 10 ms
  ([015-86](../015-todo/86-gets-with-8-readers.md), formerly 005-65). The
  rest of those gets, up to 39 ms, came with every core busy (8 readers
  and ZGC's workers on 10 cores): waits for a core, from the operating
  system's scheduling, outside BergDB's target (Frans, 2026-10-29:
  accepted as a full machine). Measured again with the fix (015-86,
  2026-11-05): the long gets' time is 99.7 percent off core, and with 7
  readers, one fewer than F53's performance cores, the fix adds none (0.4
  in a million over 10 ms); closed as explained (Frans, 2026-11-06).
* No read waits for the stream's writer since 2026-10-27
  ([005-46](../005-todo/46-stream-file-lock.md)): a read takes no lock, a
  new file is made outside the stream's monitor, and a cut's files are
  deleted by a thread of their own. Until then a read of the last file
  waited for the writer's append and its force, seconds on s1's disk, and
  every read for a cut's deletes, up to 171 ms in P4's soak (009-04,
  section 7.3): a deviation, now fixed. A writer that fills the write
  buffer still waits for the disk: the device's limit, not BergDB's work
  (005-46, decision 5).
* A deviation since 2026-11-06 (015-80): Reclaim's cut, made by a
  committing writer under the write lock, waits for the storage thread's
  append in progress and its force. An append is up to 5 MB, half the
  default buffer; one of 2.5 MB with its force took 17 ms on average and
  144 ms at the longest on F53 (005-46), and a force on s1 can take
  seconds. The other writers wait with it; readers do not. Measured
  ([019-36](../019-todo/36-reclaim-cut-waits-for-append.md), 2026-11-06
  and 07, a write load with reclaim on): on s1 at full speed 11 of 658
  cuts waited, the longest 19.85 ms; on a quiet F53, none of 913 (the
  longest 0.012 ms), and none of the paced runs' cuts on either. A cut
  comes right after the thread's append has let go of the lock, so it
  rarely meets one. Within Frans's guide (F53 under 50 ms good, s1 under
  100 ms good): no change of the code (review R4 of night 006-12, C1).
* To look at (Frans, 2026-10-26): every place where a reader can wait
  today, and for how long.
* Eviction: the sweep that walked the resident set under the write lock,
  up to 266 s in 004-02, is replaced by handles and bounded steps (item
  009, on `main` since 2026-10-26).
* The collector: ZGC, and Shenandoah in its default mode, without
  generations, meet the target in P4's soak; G1 does not
  ([004-04](../004-indirect-swizzling/04-zgc.md)), and generational
  Shenandoah stopped for 182 and 821 ms in the soak with eviction
  ([009-04](../009-handles/04-shenandoah-degenerated.md), section 8).
  Item 009's target counts BergDB's own code only, and recommends a
  collector (Frans, 2026-10-27: "The target of 20 ms is for the BergDB
  code. Not for the JVM itself.").
* A decrease of the startup distance no longer makes one long commit
  ([007-04](../007-bounds/04-review-after-009.md), points 6 and 7). Since
  2026-10-28 007-03's deadline is a backstop behind 005-49's paced take,
  in which each commit writes its share; the deadline is at the stream's
  length minus max(2 × sd, the section's span), and after a decrease the
  span shrinks with every commit (D4:B,
  [007-07](../007-bounds/07-step3-paced-take.md), section 10.1). At 10M
  keys, from 1000 to 100 MB, no record of the decrease was over 3.6 MB,
  where the patch alone wrote one of 486 MB; from 200 to 50 MB, 5.4 MB
  (007-07, section 10.4). In steady state the deadline never took a
  transaction that the share would not. Not yet known: how long these
  commits take, as the runs counted bytes only, and 50M keys, not run
  (007-07, section 10.5). The other writers wait for each commit; since
  005-46 the readers of the stream's last file do not.


P2. A deterministic stream
--------------------------

The bytes of the stream are a function of the accepted transactions,
their contents and their order, and nothing else: not of timing,
threads, restarts or the state of the cache. Given the same initial
stream and stream-affecting settings, the same ordered sequence of
accepted transactions produces the same bytes. Frans's goal of
2015-12-28: "a restart can be inserted between any two transactions
without affecting the bytes in the stream".

Acceptance need not be deterministic. STM may refuse a transaction
request because of a conflict or insufficient validation history.
Requests may also be refused because the database lacks resources.
A restart may affect which requests are accepted. Such refusals do not
violate P2: runs with different accepted transaction sequences may
produce different streams.

A refused request must leave the stream unchanged and must not affect
the bytes generated by later accepted transactions.

Separately, an RW transaction's reads, computation and commit belong
to the same running database instance (005-70, "RW lifecycle and Lean").
After closing and reopening, discard the pending read set, reread and
recompute. This API contract is independent of P2's distinction between
requests and accepted transactions.

The transactions are deterministic too: "Is a KissDB transaction always
deterministic? Answer: Yes." (2008-08-02). What may refuse a transaction
is checked before it changes anything (the go point;
[levels.md](../011-docs-archive/04-levels.md), "A transaction or a read that
fails"). A failure after that point is P7's.

Where BergDB stands:

* Proved for the abstract records: T2, restart invariance
  ([sis-model.md](../../docs/sis-model.md), section 9), on assumption A1,
  determinism of the transactions. `T2_restart` compares the same list of
  accepted transactions with and without restarts. The model has no pending STM
  read sets or admission/retry decisions; this is not a proof of STM or
  its lifecycle checks (005-70, "RW lifecycle and Lean").
* Checked for the bytes: the restart checks require byte equality
  (`RestartInvariance`, [levels.md](../011-docs-archive/04-levels.md)); the padding
  bytes that the 2017 code left uninitialized were fixed on 2026-10-12.
* Checked for the take since 2026-10-28, 005-49's paced take with 007-03's
  deadline and D4:B ([007-07](../007-bounds/07-step3-paced-take.md)): it
  reads only what a start reruns, the section's span too (section 10.1).
  StreamDigest: two runs give the same 36 streams, and in each
  configuration the plain, reads and restarts streams agree (sections 5
  and 10.3). No configuration of StreamDigest lowers the startup distance;
  a decrease with restarts during it gives the same stream, byte for byte,
  as without (`DbTesterRestart`, section 10.2).
* Checked for the buffer time on 2026-10-29 (005-64): StreamDigest with
  the tests' buffer time at 50 ms gives the same 36 streams as at 10 ms.
* Not kept across a start (005-71, option A, 2026-11-03): `DbClock`'s
  last read time, the last time `currentTime()` returned. A restart after
  a `currentTime()` that returned a time after the last transaction's,
  with a clock that has not moved since, gives the next transaction a time
  one unit earlier than without the restart, and so other bytes; the next
  transaction may then have the time that `currentTime()` returned before
  the restart (its promise, a time before every later transaction's,
  holds within a run). Accepted: a read is not a write and need not be
  durable; the transactions' times stay increasing; it needs a clock that
  does not move (a test clock, or a system clock set back), as a restart
  takes longer than a time unit (100 ns). The checks of P2 move the test
  clock before each transaction: `RestartInvariance` and `StreamDigest`
  set it 1 to 20 units after the last one before each transaction, and
  neither calls `currentTime()` (their reads give their lookup times).
* Decided in integers since 2026-11-03 (005-79): no double or float decides
  the stream's bytes or the memory in the Core. The take's share and dither
  are in units of 2^-16, as is reclaim's internal fraction; reclaim's
  iteration spacing and eviction's low watermark are integer quotients
  (R / 4, floor(3 budget / 4)). Integer operations are defined alike on
  every target, so a port (item 012) gives the same bytes with 64-bit
  integer arithmetic, with no care for fused multiply-adds, extended
  precision or a missing FPU. `java/doubles.py` checks it in
  `before-commit.sh`: it refuses floating point in the Core Layer's
  production code outside a list of allowed places (API conversions,
  statistics, the users' values as bits). Frans (016-01, D3, 2026-11-03):
  "005-79, yes implement this internally. The Pub API can use doubles at
  the interface, then immediately convert to integers (int, long)
  internally."
* Kept in the stream since 2026-11-05 (015-87): reclaim's settings, the
  retain duration and the internal fraction, which decide reclaim's
  records. A setter call that changes one commits both in the internal KV
  `/#i/dreclaim/-settings.txt`, a call with the values in force writes
  nothing, and a start reads the KV; a stream without it has the defaults
  (forever, and a quarter). Before, a start took the builder's retain
  duration and the default fraction, so a restart that did not set them
  again stopped reclaim. Checked by
  `DbTesterRestart.testReclaimSettingsKeptOverRestarts` and StreamDigest's
  mode `restarts-once` (the value set after the first start only), and by
  RestartInvariance in `level3.sh`, which sets it after the first start
  only. The step reserve (`DbBuilder.reclaimStepReserve`) is a setting for
  tests: below its default it changes the bytes, and it is not kept.
* To check: that the memory budget and eviction (Level 4, item 009) leave
  the bytes unchanged, or, where a setting changes the bytes, that the
  principle says so.


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
  buffer at the latest a buffer time (50 ms since 005-64; 20 ms from
  005-13) after the commit, and at once for a sync that waits (005-48),
  and sleeps when nothing is buffered (005-14).
* A get or a commit that needs memory, or a lower cache size
  (`Database.setCacheSizeInMb`, since 2026-10-28, 005-52): the eviction
  thread, `bergdb-evictor`, one per database (009, decision T5a), is
  started or woken. A thread is fine (Frans, 2026-10-26). When idle it
  waits with no timeout; the database's close wakes it, and it ends
  ([005-51](../005-todo/51-eviction-on-calls.md), 2026-10-27). Until then
  it waited with a timeout, `evictorLock.wait(1000)`, to see whether the
  database had stopped: one wake-up a second, as long as the database was
  open.
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

* Index nodes are written in proportion to each commit's size since
  2026-10-28, by 005-49's paced take
  ([007-07](../007-bounds/07-step3-paced-take.md)): in 007-06's and
  007-07's runs at 10M keys the largest record fell from 2.3 to 4.6 MB to
  0.23 to 1.9 MB with transactions of 1,000 puts, and from 0.73 to 0.96 MB
  to 0.23 to 0.29 MB with single puts. Before, they were written in bursts
  at the startup distances a large database should use
  ([005-49](../005-todo/49-smooth-index-writes.md), from
  [005-38](../005-todo/38-writes-at-scale.md)). A small commit after a
  large transaction can still write that transaction whole (007-07,
  sections 7.1 and 7.2), accepted for now (Frans, 2026-10-28).
* The deadline of 007-03 takes every transaction that is due, in one
  record, or a few at the record limit. After a decrease of the startup
  distance it no longer makes one long commit (D4:B, 007-07): it is at the
  section's span, which shrinks with every commit. At 10M keys, from 1000
  to 100 MB and from 200 to 50 MB, the largest record of a decrease was
  3.3 to 5.4 MB, `setStartupDistance`'s own, with the share of its 200 kB
  value, where a deadline at twice the new distance at once wrote 87 to
  486 MB in one record (007-06). Whether that value should earn a share is
  for Frans (007-07, section 10.5).
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
* BergDB's own take keeps up with 2 × sd since 2026-10-28, by 007-03's
  deadline (step 3, [007-07](../007-bounds/07-step3-paced-take.md)); after
  a decrease of the startup distance, with the section's span at the
  decrease, which shrinks with every commit. Its pace held the section at
  1.00 to 1.14 sd in 005-49's, 007-06's and 007-07's runs. Before, 005-38
  measured the take past 2 × sd at 50 and 200 MB (007-04). Proved in Lean
  for a policy that keeps up (T3), not yet for BergDB's own take: 007-03,
  step 4; [docs/levels.md](../../docs/levels.md), section 5, says so.
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
* The retain duration: `setRetainDuration` while it runs; kept in the
  stream since 2026-11-05 (015-87).
* The startup distance: `Database.setStartupDistanceInMb` while it runs,
  since 2026-10-28 ([005-53](../005-todo/53-startup-distance-on-the-fly.md),
  option E), with one call: the setting is in force when the call returns
  and kept in the stream's meta blocks, as it shapes the stream's bytes
  (P2); after a decrease the section comes down as the application
  commits, with no commit that writes the whole of it (007-03, D4:B;
  007-07). The core had it since 2013-04 (`Db.setStartupDistance`, also
  through JMX), never the Pub API until then; 006-06 (fast restart) builds
  on it.
* The cache size: `Database.setCacheSizeInMb` while it runs, since
  2026-10-28 ([005-52](../005-todo/52-cache-size-while-running.md), option
  B), for the run, as it changes no byte of the stream: the resident bytes
  converge to the new budget in the eviction thread's batches of at most 2
  ms, which the call starts, so an idle database gives the memory back too
  (Frans, 2026-10-26: "Gradual convergence to the new setting."). The rule
  for a setting changed while running: one that changes the stream's bytes
  is kept in the stream, one that does not lasts for the run.
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

A database whose environment has failed (an I/O error, corrupt data, too
little memory or stack: an `Error`), or that has a bug, does not run on.
It fails: the call throws, and so does every later transaction and read;
the application ends its process and starts the database again. "We do
not want the application to run if its environment (needed assumptions)
is faulty or if there is a bug." (2013-01); "FatalDBException - an error
happened in the database that makes it unusable. Usually handled by
logging the error and stopping the database." (2012-08). A refused
transaction is another matter: it changes nothing, and the database goes
on (P2).

Where BergDB stands: as P7 says, since 005-01 for transactions and 005-30
for reads and syncs (`DbFailedException`; [levels.md](../011-docs-archive/04-levels.md),
"A transaction or a read that fails"); since 019-10 (Frans, 2026-11-06),
for an `Error` in a read, a transaction or a sync, or on BergDB's own
threads too, thrown as it is. BergDB assumes a sound environment
(storage, memory, stack) and does not try to recover from a faulty one:
the database fails, and the application ends its process.


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
* A static set, since 2026-10-28 (005-63): `FileStream.LOCKED_DIRS`, the
  directories that the JVM's `FileStream`s hold. A second `FileStream` on
  a directory is refused there before it opens the directory's lock file,
  `bergdb.lock`: closing its channel of the file would release the first
  stream's operating-system lock for other processes (POSIX record locks
  belong to the process; seen on macOS). A deviation that Frans chose: one
  database refuses another on its own directory, in the JVM as across
  processes, and the set does nothing else.
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
  the crypto key; the clock; the startup distance (default 50 MB, clamped
  to 5 to 1000 MB); the cache size (default a fifth of the JVM's maximum
  heap). The startup distance and the cache size also change while the
  database runs (`Database`'s setters; P6). The retain duration is set
  only by `Database.setRetainDuration` and kept in the stream; its builder
  methods, `DatabaseBuilder.retainDuration` and `DbBuilder.retainDuration`,
  were removed on 2026-11-05 (015-87, Frans: "Yes, remove it from both
  layers").
* The default startup distance does not suit a large database: from about
  10M keys, 200 to 1000 MB does (005-38), chosen when the database is
  created, or later with `Database.setStartupDistanceInMb` (P6, since
  2026-10-28). A deviation. 2013-04-08: "It is not clear to me how to do
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

The Core Layer is a simple key-value datastore: both keys and values are
byte arrays. Frans (2026-11-09): "Describe Core as a simple key-value
datastore, where both keys and values are byte arrays." It adds
transactions and history (a read at a lookup time), and it never reads a
value for its meaning. Objects, their stored format (020-07), their
conversion to Java (020-09) and user indexes (020-10) belong to the layers
above: to the Core Layer an object is a byte array, and an index's
definitions and entries are keys like any other, under `/#i/`. What a
layer above needs from the Core Layer is a general mechanism that knows
nothing of its use; a new one widens the Core API, and is Frans's to
decide.

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

Where BergDB stands (`java/src`, 2026-10-28):

* The Core Layer imports no upper layer: `core` imports `common`, `dag`,
  `nanotest`, `pub.util`, `storage` and `stream`. It builds alone, a
  program calls `Db` with only the Core Layer on its class path, and each
  of its seven packages imports only what its `package.html` allows
  (006-08, which moved `FileStreamPowerLossTester`, a tester that made
  `stream` import `core` and `storage`, to `core`).
* `pub` imports no core type: `SyncLevel` is in `pub.util` since
  2026-10-28 (005-56; until then a core type in the public API).
* Every `package.html` in `java/src` lists its package's uses in one form,
  and `java/deps.py` checks them (005-56). `pub` and `pubimp` use each
  other, by design: `Factory`, and `Time`'s `TimeResolver`.
* `getOneInternal` is public.
* Release 2026.4's objects (format 2) and user indexes added no code to the
  Core Layer (2026-11-09): its changes since 2026.3 are the faults 019-46
  and 019-47 and the UTF-8 rules for keys and strings (021-04 to 021-06).
  The general mechanisms that the layers above use, all in the Core Layer
  since the 2017 baseline: a transaction's lookup time and read hashes
  (optimistic concurrency); virtual writes
  (`Trans.Builder.addVirtualWriteHash`: a hash that conflicts as a write
  does, with nothing stored; used by the index code alone, for
  `/#i/div/<dir>`, 020-10, section 5.1); key and value transformations at
  commit (`KeyTransformation`, `ValueTransformation`); and the internal key
  space `/#i/`, where the Core Layer's own keys are Reclaim's and
  `/#i/-dummy` (`core/doc-files/key-encoding.md`).
* Db has 45 public methods (43 until 005-52 added `setCacheSizeIndicator`
  and `getCacheSizeIndicator`, 2026-10-28, so that `pubimp` and JMX set the
  cache size through the Core API and not through `internal()`).

The measures: `java/deps.py` in `java/before-commit.sh`, each package's
uses against its `package.html` (005-56), and the Core Layer built alone,
with an empty class path, and its tests run on it, nightly in `night.sh`
(`java/stress/core-build.sh`, from 006-08; 2026-10-28). A candidate: the
number of Db's public methods.


P13. KISS
---------

Keep it simple: the design, the API and its error model, the code, the
tests and the tools. What is simple can be understood, checked and kept
correct, by the user of the database as by its developers. Frans
(2026-11-06): "KISS is an important principle. Important that the
database user understands the error model. That is part of the
interface." And: "Always important. Also with AI, even though more
complexity can be sustained now."

P11 is the same rule weighed against speed; P13 holds everywhere.
