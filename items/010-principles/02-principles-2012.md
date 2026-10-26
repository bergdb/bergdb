010-02. Principles of the 2012 era
==================================

Created 2026-10-26 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request: "Start a new agent in the background that searches pre-2026
bergdb, this repo and F1-007 if needed, for principles from the 2012 era."
Later the same day, through the session that started this one, he asked to
look also for the reasons behind P3: BergDB as a library, the application
deciding, no sporadic actions, and a `maintain()` call. Only reading;
nothing in the f1 archive and nothing in [01-principles.md](01-principles.md)
was changed.

What Frans wrote down from 2008 to 2017 that states a principle: a rule, a
goal, a "we want", a decision with its reason. First how it relates to P1
to P4 of 010-01 (supports, refines, contradicts), then the other
principles, then candidates for 01.


Summary
-------

* All four principles of 01 are old. 2009-11-03 has three of them in one
  entry: "only continuous operation by small computational pieces at a
  time. No stop-the-world of course. [...] it would act as a "passive"
  library." The 2012-07 reclaim note has three as well: piggy-back work
  "allows a deterministic stream (good for testing) and guaranteed zero CPU
  load when DB not used", and reclaim's writes are limited "to a factor of
  the ordinary transaction size".
* P1. The paper on self-indexed streams (May 2011) names "Limitation 1
  (stop-the-world)" of check-pointing, which continuous check-pointing
  overcomes. `Db.warmup` says, since 2014 and still today: "we keep
  variability as low as possible and focus on good worst-case
  performance". No numeric bound on a pause, and nothing on the
  collector's pauses, was found.
* P2. Deterministic transactions (2008-08-02), a deterministic stream
  (2012-05, "DONE!"), a stream that restarts do not change (2015-11 and
  2015-12-28). In 2017 Frans calls determinism "the philosophy of BergDB"
  and asks it of the cache too.
* P3. The released promise of August 2013: "No CPU usage when database is
  idle. [...] There are no long-running background threads that perform
  administrative tasks." 01's reasons are in the old texts: a library in
  the application's process (2009, 2012, 2013), work outside the calls as
  jobs the application starts and can watch (2013), and determinism for
  tests (2012, 2014, 2017). No `maintain()`, compact or idle call was
  found.
* P4. Reclaim's writes as a share of the user's writes (2009, 2012,
  `Reclaim` in 2013), and large work split into transactions of bounded
  size (2008, 2012, 2013). A 2013 note answers 007-04's point 6: decrease
  the startup distance "in steps of 1M [...] to avoid a huge transaction
  with dirty nodes".
* Where they differ: the old texts are stricter than 01 on threads
  (eviction "from Get operations", "no background thread") and on readers
  ("Readers are never blocked"). Ideas of work "when idle" or "when the DB
  load is low" (2012) were never built; in 2014 Frans rejected one because
  doing the work in the transactions "reduces some variability".
* Candidates for 01, at the end: bounded startup, readers never blocked,
  no interruption for changes, deterministic transactions and a failed
  database that stops, determinism beyond the stream, a library without
  global state, no administration, and simple before fast.


Sources
-------

Searched: Frans's notes and logs in the f1 repository's F1-007 archive, the
old Git history, this repo's `docs/sources/`, `docs/` and `items/`, the old
website on the Wayback Machine (to date the features text) and Frans's
blog. Short names below:

* `doc/`: f1 `a/007-bergdb-261012/bergdb/doc/`, Frans's notes by year,
  2012 to 2016. `doc/log-old/2008-2011-log.txt` and
  `doc/log-old/2012-log.txt` are the logs before Git; their entries are
  headed by the date (YYMMDD). Notes without a date in the text are dated
  by the file name's month.
* `log.md`: f1 `a/007-bergdb-261012/bergdb/log.md`, the main log, 2013 to
  2017; entries are headed YYMMDD/days.
* Old Git: f1 `a/007-bergdb-261012/bergdb-git.bundle`, 2013-06-06 to
  2017-08-01, files under `bergdb/`, at `49aa48d` unless a commit is named.
  The first commit, `76c4792` (2013-06-06), imported the older code, so
  "by 2013-06-06" means written on that day or before.
* The paper: "Self-indexed Streams: Append-only Storage for Large Indexed
  Data Sets", [self-indexed_streams_v5_130704.pdf](../../docs/sources/self-indexed_streams_v5_130704.pdf)
  (2013-07-04). The passages quoted are also in the draft headed "May
  2011", `doc/2013/2013-self-indexed-streams/self-indexed_streams_v4_110630.odt`.
* "BergDB features": the text of `docs/features.html` (`log.md` 130814:
  "Document: docs/features.html."). Quoted from the version headed "[By
  Frans Lundberg, August 2013]" on bergdb.com/about.html, in the Wayback
  Machine's capture of 2014-07-14; the page also has a version of March
  2014. Release 2015.4 has the text as `docs/features.html`, with small
  edits (the zip is in f1's `temp/`, not tracked).
* The blog: blog.franslundberg.com, posts on BergDB from 2013-12 to
  2015-01.

Quotes are verbatim, with the source's spelling; [...] marks a cut.


P1. No stop-the-world
---------------------

### Supports

2009-11-03, `doc/log-old/2008-2011-log.txt` line 2118, on rewriting old
data so that it can be removed:

> We write W*0.5 amount of data to refresh old data and W to write new data
> (or some other suitable factor, maybe 1.0 instead of 0.5?). NO
> checkpointing - only continuous operation by small computational pieces
> at a time. No stop-the-world of course. No maintenance really, it can
> even be embedded in calling thread so no threads need to be started by
> KissDB itself - it would act as a "passive" library.

The paper, section 2.3 (May 2011 and 2013):

> Limitation 1 (stop-the-world). The entire data set must be written to
> the stream at once to make a checkpoint (S3 and S6 in Stream 3, for
> example). During this time, no other transitions can be written to the
> stream. Normal database operations that alters the data will thereby be
> disturbed.

Its section 3.2, on continuous check-pointing:

> [...] limits the size of any element written to the stream to that of
> the largest data item. Provided the data items are small, the normal
> database operations can run without interruptions.
> There is no specific start or stop of checkpoints. Check-pointing is done
> gradually in small steps.

And section 3.4: "By using a continuous checkpoint stream, we overcome
Problem 1 (stop-the-world) of checkpoint streams."

2008-07-24, `doc/log-old/2008-2011-log.txt` lines 43-47: "In-memory serial
transactions are fast enough. Everything is normally limited by disk or
network performance rather than CPU performance anyway. However, we cannot
allow to lock whole database while data is being read from or written to
disk."

The worst case, 2008 to 2015:

* 2008-11-02, same file, lines 1698-1701, on keeping the index in memory:
  "THIS ASSUMPTION IS A GOOD OPTION. Together with big file, we get this.
  Known startup time. Known max access time (depending on higher
  level...), good for RT."
* 2012-01, `doc/2012/2012-01-optimal-tree-structure.txt` lines 22-23: "We
  want to optimize the mean cost, but also the worst case cost to access,
  add, and remove a key-value pair."
* January 2012, `doc/2012/2012-01-the-separator-problem.txt` lines 12-13
  and 30-32: "For highest performance and lowest worst-case access time, it
  is important to avoid slow disk accesses." and "Note, there is a
  difference between optimising for fastest average lookup time and worst
  case lookup time. Both of these are of importance for practical
  implementations."
* 2012-01-23, `doc/log-old/2012-log.txt` lines 149-150: "Also, some
  thought about worst-case could also be relevant."
* `Db.warmup`'s javadoc, old Git `bergdb/src/bergdb/core/Db.java`, still in
  `java/src/bergdb/core/Db.java` today. The first sentence is there by
  2013-06-06, the rest since 2014-10-31 (`eb765de`), worded as here since
  2015-08-05 (`7d13dca`):

  > We want to minimize the time holding this.writeLock. [...] But, until
  > proven important enough, we keep variability as low as possible and
  > focus on good worst-case performance.

  The wording of 2014-10-31: "focus on best "worst-case" performance
  (worst-case performance vs best-case performance)".

### Refines

**Readers.** The old texts promise more for reads than a worst case of
20 ms: a read is never blocked.

* 2008-08-06, `doc/log-old/2008-2011-log.txt` line 339: "Read transactions
  will NEVER block!"
* 2009-11-01, same file, line 2088: "* Read transactions will NEVER lock
  anything in the database."
* 2012-02, `doc/2012/2012-02-notes.txt` lines 249-251: "A set operation
  will add data to a number of nodes. We should do this as quickly as
  possible to avoid long-time locking. Remember, reads are NEVER blocked,
  locks are for set() operations only."
* "BergDB features", August 2013: "Readers are never blocked by writers or
  other readers."

Today 007-04 (points 6 and 7) records readers of the stream's last file
that wait for a long commit (005-46).

**The user's large transactions.** P1 is about BergDB's own work. In 2008
Frans saw that a large transaction of the user blocks the small ones, did
not interleave transactions, and limited their size instead.

* 2008-08-31, `doc/log-old/2008-2011-log.txt` lines 757-758, an advantage
  of overlapping transactions: "* Better realtime performance since a large
  write transaction will not block small write transactions." And lines
  768-771: "Right now, I don't see the huge advantage with overlapping
  transactions, especially when all writes done by transaction must fit
  into memory. However, not having support for this could potentially be a
  show stopper for certain types of applications."
* 2008-09-12, lines 829-830: "After discusson with Jarek I think
  transactions should be limited in size. They are written to state stream
  one by one, not interleaved."
* 2008-10-29, lines 1415-1417: "Transactions larger than 1 MiB or so would
  not be a good thing anyway, since they freeze transaction processing for
  a while."

Today 005-17 limits the size of a transaction.

**Changes while running.** Adding an index or a replica, or changing a
setting, does not stop the database.

* 2008-08-06, line 350, on a feature that can be switched while the
  database runs: "This is great, we never want to take down the database!"
* 2012-10-09, `doc/log-old/2012-log.txt` lines 1076-1078: "Not locking at
  all when adding/deleting an index is important progress :-) Actually,
  there is no such thing as locking in KissDB - nothing is locked, only STM
  is used."
* "BergDB features", August 2013: "Indexes can be added and removed with no
  locks and no interruptions of ongoing operations." and "Replicas can be
  added and removed while the database is running." (March 2014 adds "with
  no disruption of existing operations".)
* 2013-04-08, `doc/2013/2013-04-notes.txt` line 192: "It is possible to
  change startupDistance while DB is running." And lines 168-170, on a
  decrease: "For a large decrease, it could make sense to descrease
  startupDistance in steps of 1M and write a dummy transaction after each
  change. This is to avoid a huge transaction with dirty nodes." This is
  007-04's point 6, the long commit after a decrease, seen in 2013.

### Contradicts or limits

* 2012-05-10, `doc/log-old/2012-log.txt` lines 732-735, on nodes cached
  twice for historic reads: "DECISION: For now we assume the double-cached
  and double-read issues are not important enought to be handled. The
  solutions are more troublesome than the problem itself. We allow for
  worst-than-optimal cache performance when historic GETs are used for many
  different times." A worse case accepted, for historic reads.
* The collector. No old text on its pauses was found. The 2012 design left
  eviction to it: `doc/2012/2012-04-cache-eviction.txt` lines 11-12, "The
  cache eviction process works closely with Java's garbage collection."


P2. A deterministic stream
--------------------------

### Supports

* 2008-08-02, `doc/log-old/2008-2011-log.txt` lines 87-93: "1. Is a KissDB
  transaction always deterministic? Answer: Yes. This is required for the
  State Stream concept. Also, it is required for software transactional
  memories (STM). This is the approach taken by Prevayler too." This is
  the assumption A1 of T2 today.
* The paper, sections 1 and 3.3 (May 2011 and 2013): "Transactions are
  deterministic; given a certain state, applying the transaction to it will
  always yield the same resulting state." and "2. Transactions must be
  deterministic; they must produce the same next state every time they are
  executed on a specific state."
* January 2012, `doc/2012/2012-01-thoughts-on-transactions.txt` lines
  137-138: "Maybe the node formation (splitting/merging) must be
  deterministic (based on incoming transaction data only)."
* 2012-05, `doc/2012/2012-05-notes.txt` lines 23-27:

  > ---- DONE! Deterministic stream ----
  > Given a number of SET operations, make sure stream contents is
  > deterministic. This is good for testing and a nice "feel-good" :-).
  > Also, it allows us to easy compute a secure hash for a sequence of
  > database operations (at least a sequence from the very beginning of the
  > db existance).

* The test `IsDeterministic`, by 2013-06-06, old Git
  `bergdb/src-dev/bergdb/test/IsDeterministic.java` (in `java/src-dev/`
  today): "Checks whether the database stream is deterministic."
* 2014-10-31, `log.md` lines 1470-1475: "I think we should define the
  "internal state" of the Db. [...] Equal internal states before and after
  a restart is a strong invariant -- very useful when proving that the
  database actually works. Restarts can be analysed separately since they
  recover the same state."
* 2015-01-03, `log.md` lines 1234-1237: "That led me to the conclusion that
  a new node should always be stored immediately in the transaction that
  creates it. This way, we get less variability, and more invariants to
  lean on."
* 2015-11, on ISSUE151111 (worked on 2015-11-14 to 16),
  `doc/2015/2015-q4-notes.txt` lines 205-207 and 219-223: "The resulting
  situation is that an ordinary transaction and a rerun transaction will
  cause a different set of index nodes to be added to the got-dirty nodes.
  *Not* acceptable!" and "* Make BergDB stream unaffected by restarts! Can
  we make sure restarts never affect a single byte of the database stream?
  No matter where a restart takes place (between every transaction, or
  never) the stream would be the same. Would make life / testing easier."
* 2015-12-28, same file, lines 164-168: the goal that 01 quotes.
* 2016-03-25, `doc/2016/2016-easter-plan.md` lines 111-118: the same goal,
  with its reason: "Reason: one more invariant to rely on. Simplifies
  significantly. Restarts can be tested orthogonal to other testing. Also,
  I know no other solution. The current approach is imply wrong."

### Refines

**Determinism beyond the stream.** In 2017 Frans calls determinism the
philosophy of BergDB, and asks it of the cache, not only of the stream.

* 2017-07-30, `log.md` lines 111-118: "Exact results are
  non-deterministic. Current caching uses WeakReference, is
  JVM-implementation specific. It is non-deterministic which defies the
  philosophy of BergDB. For testability etc, we want perfect determinism.
  We also want a cache that keeps track of exact sizes." With the to-do "*
  Implement a deterministic cache (ref counting)." (`Cache3`, old Git
  `9d9a038`, 2017-07-30: "A deterministic node cache; size is known, weak
  references are *not* used.")
* 2015-01-03, `doc/2015/2015-q1-notes.txt` lines 100-101: "Note that if we
  wrap INode in a SoftReference, we loose our deterministic approach. JVM
  will evict, no full control."
* 2012-06, `doc/2012/2012-06-notes.txt` lines 86-97, of four ways to limit
  the cache, the fourth: "4. is useful because it is not dependent on the
  JVM memory usage. Also, it can be deterministic. Good for testing."
* 2008-11-12, `doc/log-old/2008-2011-log.txt` lines 1845-1847: "Conclusion:
  We need a cache with more control than weak references provide. We want
  to evict cache entries when required, not before that."

01 asks that eviction leave the bytes unchanged ("To check"). The 2017 text
asks more: that the cache itself does the same in each run.

**The clock and the database ID are inputs.** The transaction time comes
from the clock and the stream holds the database ID; tests fix both. By
2013-06-06, old Git: `CoreTestClock`, "Deterministic clock suitable for
testing."; `DatabaseId.TEST_ID`, "A database ID used for testing; useful
to have deterministic stream bytes and to avoid overhead of creating a new
one." And [2015-algos.pdf](../../docs/sources/2015-algos.pdf) (dated 3 March
2016), section 4: "For testing purposes, it is useful to be able to use
custom (deterministic) Clock implementations." So "a function of the
transactions" counts the transaction times, and the database ID, among the
inputs.

### Contradicts (early ideas, given up)

* 2008-11-02, `doc/log-old/2008-2011-log.txt` lines 1719-1720, in "IDEA:
  Usage-dependent compounding (merge/split)", on when to merge or split
  nodes: "Kiss for user would be if database determines this from usage so
  programmer does not have to deal with this." Splits from read and write
  statistics would make the stream depend on reads and on timing. 2012-01's
  node aggregation by access cost
  (`doc/2012/2012-01-node-aggregation-based-on-cost.txt`) is the same idea.
  The same month's note above asks for node formation "based on incoming
  transaction data only".


P3. Calm when not used
----------------------

### Supports

* 2009-11-03 (under P1): "No maintenance really, it can even be embedded in
  calling thread so no threads need to be started by KissDB itself - it
  would act as a "passive" library."
* 2012-07 (the algorithm is dated 2012-07-17),
  `doc/2012/2012-07-space-reclaim.txt` lines 75-77: "* The algo could run
  "piggyback" on existing transactions. This allows a deterministic stream
  (good for testing) and guaranteed zero CPU load when DB not used. Having
  no background threads is a tempting proposal."
* 2013-01 (about 2013-01-25), `doc/2013/2013-01-notes.txt` lines 74-85:

  > Of course, we could introduce a background thread to do evict, but we
  > like the piggy-back approach. When not used the database should take
  > very little resources. KissDB functions more like a library, than a big
  > separate process. Eviction should be made from Get operations. Since
  > Get operations cause caching, it is reasonably that Get operations also
  > can cause cache eviction. We could have a database with no writes for a
  > while and then it is not acceptable to let the cache grow out of
  > control.
  >
  > What we want from evict():
  >
  > * Fast - should not limit performance much (10% acceptable).
  > * Piggyback - no background thread. Keeping with "tradition".

* `Reclaim`, by 2013-06-06, old Git `bergdb/src/bergdb/core/Reclaim.java`
  (in `java/` today): "130129 Frans. [...] Current implement does not start
  new threads, but runs piggyback in the thread that executes an ordinary
  external transaction."
* "BergDB features", August 2013, under "5. Unobtrusive" ("BergDB is a
  small library that tries to get out of your way."):

  > No CPU usage when database is idle. BergDB consumes CPU cycles only
  > when it is actually used. There are no long-running background threads
  > that perform administrative tasks. All work is done when the database
  > library is called from ordinary application threads.

* The test `FileSynchPerformance.testWait`, by 2013-06-06 (in
  `java/src-dev/` today), measured it: "Tests whether consumer thread
  causes any significant CPU load when idle." Its recorded result: 0.07 to
  0.08 s of CPU in 20 s, at buffer times of 10 to 100 ms.

### The old reasons for P3

01's "Why" (2026-10-26) has three reasons. All three are in the old texts.

**A library in the application's process.**

* 2009-11-03: "it would act as a "passive" library" (above).
* 2012-08, `doc/2012/2012-08-notes.txt` lines 46-48 (and 2012-09): "The
  error handling is handled through ordinary Java exception handling. The
  KissDB database is (when used in-process at least) just a library like
  any other Java library."
* 2013-01: "KissDB functions more like a library, than a big separate
  process." (above)
* April 2012, `doc/2012/2012-04-cache-eviction.txt` lines 30-33, against
  evicting by the JVM's free memory: "The drawback is that the JVM may be
  used for other purposes too (in-process database use) and other code
  could use a similar approach which could become problematic. Also the
  code become dependent on the JVM."
* 2013-01, `doc/2013/2013-01-notes.txt` lines 287-292, on warnings: "The
  benefit with Solution 1 is that it is code-only. Not shared state.
  Configuration of warning-handling can be done per-DB (not per thread)
  without affecting configuration of other DB instances or user code
  application code. It makes more sense to set warning-handling per-DB,
  instead of per thread. One thread may make calls to multiple DB instances
  and other user-specific application code."
* The `bergdb.dev` package doc, by 2013-06-06 (unchanged in
  `java/src-dev/bergdb/dev/package.html`): "BergDB should run well in the
  same JVM together with other software."
* "BergDB features", August 2013: "In-process. BergDB is designed for
  application databases and runs in the same process as the application
  code for highest possible performance and reduced complexity."

**The application decides, visibly.** Work outside the calls is a job that
the application starts and can watch; settings are in its code.

* 2013-03, `doc/2013/2013-03-notes.txt` lines 96-98 and 126-128: "The
  concept of database jobs. Background jobs started with a call to Database
  or Connection. Can be queried for progress and we can wait for them to
  finish." Used for "* Index building. * Index deletion. * Add replica."
* 2012-09, `doc/2012/2012-09-index.txt` lines 135-137: "If the user wants
  to, he can request the index to be generated from existing data. While
  that happens (in a separate thread) the index is in state "Creating"."
* 2013-01, lines 55-60: "Since KissDB works as a library API and to KISS,
  it may make sense to limit the number of persistent settings. For
  example, the database will be started and then DB.setRetainDuration() may
  be called in the startup "script" (or "startup code"). Maybe such
  settings are suitable to store in code?"
* "BergDB features", August 2013, "No global state": "BergDB is controlled
  completely through ordinary code."

**No sporadic actions: tests and determinism.**

* 2012-07: piggy-back work "allows a deterministic stream (good for
  testing)" (above).
* 2014-11-01, `log.md` lines 1446-1454:

  > In a way, I like the idea of decoupling kvTransactions from internal
  > indexTransactions due to startupPos increase. The piggyback approach is
  > not the only possible approach; decoupling would allow experimenting
  > with other approaches. For example: write index transactions in
  > background when db usage is low. But, putting them together reduces
  > some variability and might be easier for me to handle; especially the
  > startup transaction reruns.
  >
  > DECISION: Go for merged storeKv/storeIndex nodes approach. A more
  > decoupled approach could be entertained once everything works.

* 2017-07-30: "For testability etc, we want perfect determinism." (under
  P2)
* "BergDB features", August 2013: "Easy to test. The database has been
  designed with testability in mind. Empty, in-memory test databases can be
  created quickly and run in your ordinary automated test code."

**A `maintain()` call.** None was found: no call in the Pub API, the notes
or the logs by which the application gives BergDB time for maintenance (a
maintain, compact or idle call). The nearest:

* the jobs above, started and watched by the application; in the Pub API
  of 2017, `Database.deleteIndex` and `Database.addReplica` return a `Job`;
* 2008-11-13, `doc/log-old/2008-2011-log.txt` lines 1861-1862, in a map
  class of 2008: "My new idea is to estimate averageKeyMemory and
  averageValueMemory while traversing the map for household tasks (step()
  method)." Who calls `step()` is not said;
* `Reclaim.step(writeSize)`, by 2013-06-06, which the transactions call,
  not the application.

2009-11-03 points the other way: "No maintenance really".

### Differs

**Stricter than 01 on threads.** August 2013: "There are no long-running
background threads that perform administrative tasks. All work is done when
the database library is called from ordinary application threads." 01
allows a thread of BergDB's own that the calls trigger. Eviction in
particular: 2013-01 wants it "from Get operations", with "no background
thread"; 009's `bergdb-evictor` is a thread (decision T5a), fine with Frans
on 2026-10-26. The old exceptions are all on 01's list:

* a thread per stream for buffered writes: 2012 (probably December; the
  2012 log's 121213: "Work on MainStream, StreamManager... Replication,
  durability control."), `doc/2012/2012-stream-manager.txt` line 86: "Child
  streams should have a thread of their own that writes to actual output.";
  2013-02, `doc/2013/2013-02-notes.txt` lines 11-12: "BufferedStream
  threads started in DB.start() or when replica is added. Objects destroyed
  at DB.stop() or when replica removed.";
* the jobs (above);
* the release after `stop()`: the `Database.stop()` javadoc, old Git: "This
  method returns quickly. It does not wait until resources have been
  released; this will happen asynchronously in the background."

**BergDB deciding by itself.** Some old ideas let the database adapt on its
own, where 01 lets the application decide:

* 2008-08-02, line 134: "* Self-tuning"; 2008-08-11, lines 559-560:
  "KissDB is an easy-to-use, secure, fast, scalable database with a high
  uptime. It is self-tuning and requires no database administration."
* 2008-08-06, line 354: "A smart, self-optimizing database can turn this
  feature on/off automatically."
* 2008-11-02 (under P2): "Kiss for user would be if database determines
  this from usage so programmer does not have to deal with this."
* 2012-07, space reclaim line 73: "* The algo thread would run only when
  "low load" is measured somehow."

**Work at idle time: ideas, not built.** They contradict P3, and P4 too:
the work would depend on the load, not on the calls.

* January 2012, `doc/2012/2012-01-thoughts-on-transactions.txt` lines
  114-115 and 150-151: "This is lazy writing of nodes. It provides a fast
  immediate write approach. Good for bursts. Node writes could be done
  later when idle." and "A node can at the same time be marked for a split
  on the to-do list of the database. Done when DB is more idle."
* 2012-01, `doc/2012/2012-01-study-on-trees-for-kissdb.txt` lines 58-60:
  "Merging all deltas of a node with the last node state in the stream and
  write it to the front of the stream is possible and it can be done when
  the database is idle."
* 2012-05, `doc/2012/2012-05-linear-search.txt` lines 18-19: "Deferred
  splits. Could be done, just allow array to grow longer but add a split
  task to a global task-queue. Run when the DB load is low."
* 2012-07, space reclaim lines 66-73: a separate thread, "with low prio to
  interrupt ordinary db execution less", or one that runs "only when "low
  load" is measured somehow".
* 2012-09, index note line 149: "NOTE, we could do this lazily in the
  background (piggyback on other transactions) or more eagerly."
* 2015-algos (3 March 2016), section 13: "An index transaction may be
  executed as an add-on (piggy-back) to a kv transaction. It could also be
  executed independently of kv transactions, initiated by the database
  itself."
* 2014-11-01: considered and rejected (above).

What was built: reclaim and the index writes piggy-back on transactions,
and an index is built in a job that the application starts.

**Library or server.** Before 2013 a server was not ruled out:

* 2012-08, `doc/2012/2012-08-layers.txt` lines 30-33: "There is possibly
  two variants of Public, one for in-process access and one for accessing
  DB that runs in a separate process. We should try to make a unified
  interface to allow easy switching between in-process and network access.
  Network access have low priority now, however."
* 2012-02, `doc/2012/2012-02-two-level-stm.txt` lines 28-30: "We assume
  that client is either in-process or in an external process. So, the
  possibility to serialize data between client and DB is required."

From 2013 the released library is in-process: "Embedded" in the design
philosophy of 2013-08-12, "In-process" in "BergDB features".


P4. Maintenance proportional to the user's work
-----------------------------------------------

### Supports

* 2009-11-03 (under P1): "We write W*0.5 amount of data to refresh old data
  and W to write new data [...] only continuous operation by small
  computational pieces at a time."
* 2010-05-10, `doc/log-old/2008-2011-log.txt` line 2225: "I use a startup
  distance (for example 100 MB) and "continous checkpointing". I like this
  approach. There is a nice flow without the explicit ..." (the sentence
  ends so in the source).
* 2012-07, `doc/2012/2012-07-space-reclaim.txt` lines 79-89:

  > * The amount written to stream by this reclaim algo should be limited.
  > It seems reasonable to limit it to a factor of the ordinary transaction
  > size. For example, if 10 MB of ordinary transactions have been added,
  > maybe 5 MB of reclaim transactions would be allowed (50%). This way, at
  > most 50% of the writes are due to space reclamation. [...]

  And lines 157-158: "Do this iteration "slowly" in a manner the rewrite
  transaction will not occupy more than 40% of the stream."
* `Reclaim`, by 2013-06-06, old Git: in `gotExternal`, "// reclaimSize is
  the size currently allowed for space reclaim transactions."; in the
  class note, "The method setInternalFraction() is available to the user. A
  large internal fraction will result in a smaller stream size, while a
  small internal fraction will reduce the amount of data written to the
  stream."
* 2013-01, on eviction: "* Fast - should not limit performance much (10%
  acceptable)." (under P3)
* The paper's continuous check-pointing (under P1): "limits the size of any
  element written to the stream to that of the largest data item".

### Refines

**Large work in bounded pieces.** Work that is large by nature is split into
transactions of bounded size.

* 2012-10, `doc/2012/2012-10-notes.txt` lines 134-137: "Can we create an
  index for existing KVs while KVs are added, modified, deleted? We cannot,
  in general, create an index as a single transaction since the size of
  the transaction would be too large."
* 2013-04-08: decrease the startup distance "in steps of 1M [...] to avoid
  a huge transaction with dirty nodes" (under P1).
* 2008-09-12 and 2008-10-29: the user's transactions limited in size (under
  P1).

**Maintenance by the kind of call that causes it.** Gets evict; they do not
write.

* 2013-01, lines 77-78: "Since Get operations cause caching, it is
  reasonably that Get operations also can cause cache eviction." And lines
  120-125: "In the new algorithm, dirty nodes are never evicted. This is
  not needed. [...] This simplifies significantly. We never have to write
  nodes to stream in the evict algorithm!"
* 2012-05-15, `doc/log-old/2012-log.txt` lines 760-762: "Consider a
  read-only DB application. It needs a dynamic cache, but there should be
  no need to write to stream when no modifications are made."

**A fixed share, not a setting.** 2012-07, lines 86-89: "I believe this can
be hardcoded to something between 0.4 and 0.7. Needs testing/experience.
But probably not needed as a setting for the end user programmer. Not
important enough; a fixed setting should work reasonable in 99 per cent of
the cases." By 2013 the share was a setting (`setInternalFraction()`).

### Contradicts

The ideas of work at idle time (under P3, "Differs"); none was built.


Other principles
----------------

### The design philosophy of 2013-08-12

`doc/2013/2013-q3-notes.txt` lines 29-43. The same day `log.md` (130812)
has "Some work on documentation: docs/design-philosophy.html."; no copy of
that page was found, in Git or on the Wayback Machine. "BergDB features"
of August 2013 has the headings simple, secure, fast, unobtrusive.

> * Fast   - append-only only way to achieve fast enough on rotational
>   storage.
> * Persistant - perstant data structure, replication, live backup
> * Secure - durable, encrypted
> * Simple
> * Embedded
> * Cross-platform
> * Code-only
>
> Inspired by: Prevayler (prevayler.org), BerkleyDB,
> "How to make data structures persistent".

### Simplicity: KISS

The database was KissDB until July 2013.

* 2008-07-13, `doc/log-old/2008-2011-log.txt` line 4: "Keep-it-simple
  solution:"
* 2008-08-02, line 100: "SQL is not a KISS approach. It is too
  complicated." And lines 133-137, the "sweet spot": "* Easy to use
  (KISS!) * Self-tuning * No db administration * Short example code *
  Sensible defaults".
* 2008-08-11, lines 594-596: "I am uncertain, so KISS should decide. KISS
  for user => no transaction description language, just Java (or C Sharp,
  or...)"; 2008-08-16, line 604: "I will go for Alternative B. This keeps
  it as simple as possible for the user."
* 2008-10-18, lines 1253-1256: "Discussion with Anton. Conclusion: do NOT
  ever change encryption key of stream. This CAN be done while the
  database is running, but it complicates for administrator of the
  database. The real security may actually be lower because of increased
  risk of administration mistakes."
* 2010-05-17, line 2288, an email: "I realized that append-only storage is
  the way to solve this without drowning in complexity."
* 2011-08-02, line 2500: "Yes, I should do this :-). BUT, very KISS to
  start with."
* 2012-01-03, `doc/log-old/2012-log.txt` line 21: "As simple as possible.
  Prioritize easy-to-read code over performance."
* 2012-08-13, lines 923-924: "We should keep Core < 50 k including tests.
  Upper independent layers can grow independently."
* 2012-12, `doc/2012/2012-12-notes.txt` line 87: "Remember to KISS."

**Simple before fast, with a price.** From 2013 Frans names the speed he
would give for simple, correct code.

* 2013-09, `doc/2013/2013-q3-notes.txt` lines 12-13: "A slower performance
  is OK. We have CorePerf factor of 0.90 now. I would trade to 1.50 for
  bug-free, easy-to-maintain and understand code."
* 2014-01-24, `log.md` line 1815: "FIGHT COMPLEXITY AND UGLY CODE! And keep
  dev.CorePerf ok."
* 2015, fourth quarter, `doc/2015/2015-q4-notes.txt` lines 114-117:
  "Correctness! An ELEGANT, SOLID core. Testable, simple, flexible. A < 2.0
  factor performance degradation compared to now is OK if we can achieve
  this."
* 2016-03-25, `doc/2016/2016-easter-plan.md` lines 11-16 and 23: "Focus: A
  CORRECT and ELEGANT core. Simple, testable, flexible. * No known bugs. *
  Improved testing. * Cleaner code (performance can be traded for
  elegance)." and "Perf: A performance degradation of up to x 2.0 is OK."
* For one hot path the other way: 2014-01-24, `doc/2014/2014-q1-notes.txt`
  lines 47-48: "Clean code is important and performance is even more
  important for the serialization."
* 2015, fourth quarter, lines 182-183: "Working with BergDB 1 or 2 days a
  month is really hard or impossible. It is not simple and stable enough
  for one-day-at-a-time work. Too complex."

### Append-only, and the history kept

* 2008-08-23, `doc/log-old/2008-2011-log.txt` lines 663-664: "The SS
  storage is write-once storage for highest performance and for storing
  previous states."
* 2010-05-14, line 2246: "Database researcher Jim Gray wrote "Update in
  Place is a Poison Apple". Yes indeed!"
* 2010-05-17, line 2290, an email: "A compact append-only stream is a
  requirement."
* The paper, section 1: on losing the changes since the last backup, "This
  is sometimes acceptable. But in this paper, we do not accept this.
  Instead we study data structures that can be replicated easily." Its
  three requirements: "1. The startup distance should be small. [...] 2.
  The stream overhead should be small. [...] 3. All states that ever
  occurred should be recoverable from the stream."; and "For typical
  database applications, we want a stream overhead that is less than 0.7."
* 2012-08-27, `doc/2012/2012-08-27-email-to-risch.txt` lines 10-17, in
  Swedish: "hur man kan konstruera en databas för våra krav: tusentals
  betalningar per sekund, replikering, högsta säkerhet, log på alla
  förändringar." (how a database can be built for our requirements:
  thousands of payments a second, replication, the highest security, a log
  of all changes) and "Lätt att ta backup online, lätt att replikera,
  snabbt eftersom man eliminerar disk-seek för skrivningar, alla
  förändringar lagras." (easy to back up online, easy to replicate, fast
  because disk seeks for writes are removed, all changes are stored).
  Translations ours.
* 2014-05-08, the blog, *There Is No "Now"*: "This is one of the reasons
  why databases should be append-only (called "immutable" by some) and
  support historic queries. They should remember the history. This is the
  only thing that can be globally agreed on."
* 2016-05-05, [startup.md](../../docs/sources/startup.md) lines 78-85:
  "1. DB must handle the case when G is much larger than the memory of the
  computer. 2. DB must support *historic queries*. 3. DB must store its
  state purely append-only to *the database stream*, S. 4. The startup
  time of DB must be O(1), or at least not greater than
  O(log(G.size()))."

### Bounded startup

* 2008-08-23, `doc/log-old/2008-2011-log.txt` lines 656-657: "It is
  important to be able to avoid reading the whole SS to startup the
  database."
* 2008-09-12, lines 839-841: "Today I got a NICE idea. I think it is simply
  put the fastest possible way to get a database started. The startup time
  would never be more than 1 second! Even for a Peta byte of data or
  something."
* 2008-11-01, lines 1607-1608 and 1615: "Theoretically, a database based on
  an Index Tree could startup in a second independent of data size
  (O(1))." and "We have to weigh fast startup versus small state stream
  size and fast writes."
* "BergDB features", August 2013: "Fast startup. BergDB has a unique design
  that allows it to have a short and constant startup time (O(1) in big O
  notation). This is important as your data grows."
* 2015-algos (3 March 2016), section 13: if the database were always
  started from the beginning of the stream, "This is not a viable approach
  as the startup time grows without bound."
* startup.md, requirement 4 (above).

Today this is item 007 (T3).

### Transactions

* 2008-08-02, `doc/log-old/2008-2011-log.txt` lines 107-114: "3. Support
  for rollback? Answer: No. If transactions are deterministic, we don't
  need this, we can always check input data before we start to modify
  data. Note, this may disallow the KissDB to participate in distributed
  transactions." (Cited in [levels.md](../../docs/levels.md), "A
  transaction or a read that fails".)
* 2008-07-24, lines 44-45: "In-memory serial transactions are fast enough.
  Everything is normally limited by disk or network performance rather
  than CPU performance anyway."
* The `bergdb.dev` package doc, by 2013-06-06: "Serial writes. While many
  transactions (both read and write) may run in parallel, write
  transactions are serialized for storage."
* 2013-12-13, the blog, *"ACID" Does Not Make Sense*: "The database I am
  working on, BergDB, only supports the strongest isolation level:
  SERIALIZABLE. Actually, the only way to change the state of the database
  is through strong transactions."

### A failed database does not run on

Cited in [levels.md](../../docs/levels.md), "A transaction or a read that
fails".

* 2012-08, `doc/2012/2012-08-layers.txt` lines 99-100: "FatalDBException -
  an error happened in the database that makes it unusable. Usually
  handled by logging the error and stopping the database."
* 2012-08, `doc/2012/2012-08-notes.txt` line 52: "KissError is used to
  assert state. Should never be thrown from bug-free software."
* 2012 (probably December), `doc/2012/2012-stream-manager.txt` lines 64-67:
  "Some streams can be allowed to fail (replicas), while another might be
  essential (it might be the only stream that can be read from. A failed
  stream will never be in ok state again. It should be removed and added
  again ("remounted")."
* 2013-01, `doc/2013/2013-01-notes.txt` lines 268-271: "Errors (unhandled
  exceptions) should be handled by simply logging the error (maybe print
  to System.out) and exiting from the application. We do not want the
  application to run if its environment (needed assumptions) is faulty or
  if there is a bug."
* `DbException`, by 2013-06-06, old Git: "This exception should be
  considered fatal to the database. That means that after a DbException,
  the database should not be considered functional and should not be used
  anymore."

### A library without global state

* The `bergdb.dev` package doc, by 2013-06-06, unchanged in
  `java/src-dev/bergdb/dev/package.html`: "Global stuff / static. Do not
  use JVM global stuff (non-final "static" fields). It should be possible
  to run multiple BergDB instances in one JVM. Easy testing, limited
  dependencies. BergDB should run well in the same JVM together with other
  software. So no global state is set by BergDB (for example: default
  exception handler, logging)." And: "Logging. Do not use java.logging.
  This is global stuff, and its benefits does not outweigh the added
  complexity, especially when BergDB is used in-JVM with other applications
  and other BergDB instances." And: "System.out is never used. System.err
  is never used. System.in is never used."
* "BergDB features", August 2013: "No global state. BergDB do not use any
  global state. It does not use custom classloaders or set
  UncaughtExceptionHandler:s. It does not use System.out/out/err. There is
  no use of global logging, environment variables, command line arguments,
  files with settings. BergDB is controlled completely through ordinary
  code. Multiple instances of BergDB can run in the same process without
  problems."
* 2013-02, `doc/2013/2013-02-notes.txt` lines 51-52: "No internal thread
  (e.g. consumer in BufferedStream) should have a reference to DB. If it
  does, DB will never be available for garbage collection."

### No administration, few settings

* 2008-08-02: "* Self-tuning * No db administration [...] * Sensible
  defaults" (above).
* 2013-01, `doc/2013/2013-01-notes.txt` lines 18-21: "Constant settings.
  Settings that are constant for the while lifetime of the database
  including restarts. These constants should be avoided whenever possible.
  Difficult to maintain as KissDB software evolves."
* "BergDB features", August 2013: "Zero database administration. Database
  administration is never needed and there are few settings. There is no
  need to spend time optimizing settings to reach high performance; most
  often, the default settings are fine."
* 2013-04-08, `doc/2013/2013-04-notes.txt` lines 179 and 194: "Should we
  have automatic increases / decreases of startupDistance? I do not know
  how to do this best." and "It is not clear to me how to do automatic
  startupDistance changes based on db size."

Today a large database needs a startup distance chosen for it, 200 to
1000 MB (005-38).

### Durability, replication, security

* 2008-08-02, `doc/log-old/2008-2011-log.txt` lines 139-146: "* Secure *
  ACID transaction support * Serializable isolation level * Support for
  encrypted storage * Real-time replication * Built-in durable storage RAID
  * Hot backup * Flexible commit control".
* 2012 (probably December), `doc/2012/2012-stream-manager.txt` lines 72-76:
  "Clients may choose to wait for different levels of durability: D1, D2,
  D3? [...] D1 would mean: "survives process", D2 would often mean
  "survives OS", and D3 would mean highest available durability achieved."
* "BergDB features", August 2013: "Durability control. Different
  transactions may require different durability guarantees. [...] This
  feature is important for high-value financial transactions." And: "Crash
  proof. BergDB never really crashes even if the process suddenly halts or
  the power is cut to the computer. The database will still startup the
  ordinary way. There is never any need for a special recovery procedure."
* An idea of 2013-11-09, `doc/2013/2013-backlog.txt` lines 90-95: "By
  never reading non-durable states, we are really sure not to expose any
  data that will not survive a crash to the end user. Note that this means
  a client may not see his writes."
* 2013-05-09, `doc/2013/2013-05-notes.txt` lines 11-14: "IMPORTANT ISSUE.
  Can we keep an active replica (available for queries) based solely on
  the replicated database stream? I never thought of designing the stream
  for this. The possibility of having active, read-only replicas seems
  important."
* 2014-07-20, the blog, *Database Mathematics*: "Durability could be
  defined using probability theory."

### Performance and scale

* 2008, `doc/years.txt` lines 122-124, a later summary (when it was written
  is not known): "Current databases are just too complicated and slow;
  seldom limited by real limits of computers, but by the implementation /
  algorithms chosen."
* 2012-01, `doc/2012/2012-01-study-on-trees-for-kissdb.txt` lines 51-52:
  "We want writes to be very fast and limited by disk. We want the stream
  to be space efficient."
* The `bergdb.dev` package doc, at `49aa48d`; the sentence on one code base
  is from 2014-07-20 (`f66bdc6`): "The database performance is optimized
  for a modern 64-bit server. Typically 4 to 16 cores. 1 to 2 CPUs. SSD or
  ordinary disk(s). But the database also has good performance on very
  small devices. There is only one code based; no differentiation between
  large server and small devices (Android phone for example)."
* 2013-03, `doc/2013/2013-03-notes.txt` lines 65-71: "But, in a huge
  database, we don't want to deal with small files (1 MB). [...] We do not
  expect larger DBs than 10 TB." and "So, how to make this work for both
  tiny DBs (0.1 MB) and huge ones (10 TB, 100 million times larger)?"
* "BergDB features", August 2013: "Scalable. BergDB is suitable for
  applications storing small amounts of data, say 1 kB. Yet, it scales to
  store terabytes of data in billions of entries." And: "The only way to
  achieve high throughput of ACID transactions (over 1000 transaction/s) to
  rotating drives is to store the data append-only."

### One stream format, every platform

* 2008-08-07, `doc/log-old/2008-2011-log.txt` lines 407-408: "Answer: NOT
  java dependent, should work with many languages with a
  language-independent data object model."
* The `bergdb.dev` package doc, by 2013-06-06: "There is only *one* DB
  stream format for all supported devices, operating systems and
  programming languages."
* "BergDB features", August 2013: "The on-disk storage format is identical
  for all platforms and therefore interoperable."
* 2012-12, `doc/2012/2012-12-notes.txt` lines 17-18: "And we do not want to
  depend in usage of Oracle's JVM."

### The Pub API

* 2012-08, `doc/2012/2012-08-layers.txt` lines 25-27: "Public interface to
  the database. Should remain fairly stable. [...] The user of this layer
  cannot destroy the integrity of the database." And lines 57-59, of the
  layer below: "The DB layer is designed to suit the DB layer
  implementation; not to suit the user of the layer. Anything that can be
  done by a user of this layer, should not be offered by this layer."
* 2012-02, `doc/2012/2012-02-notes.txt` lines 203-205: "What is the minimum
  required interface to the database? Only what would need to be
  serialized (if accessed over network) is considered. Everything the
  client can do itself, is put on the client side."
* 2012-10-18, `doc/log-old/2012-log.txt` lines 1113-1114: "He says, avoid
  using more than 3 parameters to methods. I checked, and no method in the
  Pub API has more than 2 parameters :-) Nice."
* 2013-03-05, `log.md` line 3496: "Easy to add, impossible to remove."
* 2013-05-30, `log.md` line 2789: "Not because I like it, because it is
  less surprising (principle of least surprise)."
* 2014-07-13 and 18, `doc/2014/2014-q3-notes.txt` lines 82 and 97: "I
  don't like that Database can be unstarted." and "Implemented at the Pub
  Layer. A Database is always started."
* 2012-11, `doc/2012/2012-11-notes.txt` line 169: "DECISION: Spatial index
  should *not* be implemented until requested."
* "BergDB features", August 2013: "Low-level. BergDB is a simple, low-level
  database library. It does one thing only: store data." And: "Small API.
  The BergDB Pub API - the standard API - is small and is designed to be
  easy to use. It is designe to be unobtrusive to your brain."
* 2015-07-29, old Git `bergdb/src/overview-pub.html`: "The goal is to keep
  things simple so that you can focus on your specific application rather
  than on struggling with database issues."

### Testability, rigor, repeatable measurements

* "BergDB features", August 2013: "Easy to test." (under P3)
* 2013-01, `doc/2013/2013-01-notes.txt` lines 173-175: "I have often
  assumed "eventual visibility". In practice, this seems fine, but we
  should avoid assuming this for KissDB. Better to implement this really
  carefully and correct. Synch bugs are the hardest."
* 2013-10-27, `log.md` lines 2071-2074: "define the invariants (the laws)
  and reason about that they are kept for all changes. [...] Could we prove
  our code is correct? (At a high level of abstraction assuming low-level
  code (like the JVM, the Java libraries) work)."
* 2015-04-26, `doc/2015/2015-q2-notes.txt` lines 10-12: "We need: * More
  formal DagSequence/startup. Think more. Invariants, strict rules,
  well-defined terms. Proof?"
* 2015, fourth quarter, `doc/2015/2015-q4-notes.txt` lines 17-18:
  "Hopefully they are correct. Can we verify this? Before expensive
  coding?"
* 2014-07-20, the blog, *Database Mathematics*: "We need mathematical rigor
  in the theory of databases."
* 2013-12-05, the blog, *Welcome!*: "If there are experiments (performance
  tests, for example), I intend to make sure they are possible to repeat."


Candidates for 01
-----------------

Principles in the old sources that 01 does not state yet, for Frans to
decide on. Each with its main sources above.

1. **Bounded startup.** Startup time does not grow with the database:
   "The startup time would never be more than 1 second! Even for a Peta
   byte of data" (2008-09-12); "a short and constant startup time"
   (2013-08); "must be O(1), or at least not greater than O(log(G.size()))"
   (2016-05-05). Item 007 works on it.
2. **Readers are never blocked.** P1 for reads, stricter than 20 ms: "Read
   transactions will NEVER block!" (2008-08-06); "Readers are never
   blocked by writers or other readers." (2013-08). Today readers of the
   last file can wait for a long commit (005-46, 007-04).
3. **No interruption for changes.** Indexes, replicas and settings change
   while the database runs: "we never want to take down the database!"
   (2008-08-06); "no locks and no interruptions of ongoing operations"
   (2013-08); large changes in bounded steps (2012-10, 2013-04).
4. **Deterministic transactions; a failed database stops.** No rollback,
   input checked before anything changes, a fatal error stops the database
   (2008-08-02, 2012-08, 2013-01). In levels.md today; P2 rests on the
   first part (A1).
5. **Determinism beyond the stream.** "For testability etc, we want
   perfect determinism" (2017-07-30): a cache with exact sizes, nothing
   that depends on the JVM's memory (2008-11-12, 2012-06, 2015-01-03). A
   wider P2, or part of P3's "no sporadic actions".
6. **A library without global state.** Several databases in one JVM; no
   global settings, logging or `System.out`; controlled through code
   (`bergdb.dev`, by 2013-06-06; "No global state", 2013-08). Part of P3's
   "Why" now; could be a principle of its own.
7. **No administration.** Few settings, defaults that work: "There is no
   need to spend time optimizing settings to reach high performance"
   (2013-08); "Self-tuning", "Sensible defaults" (2008-08-02). The startup
   distance of a large database is such a setting today.
8. **Simple before fast.** Correct, simple code first, at a price in speed
   named in advance: 1.5 (2013-09), 2.0 (2015, 2016-03-25). About the
   development, not the behaviour; 010's scope decides whether it belongs.


Outcome
-------

Frans's decisions, 2026-10-26, written into [01](01-principles.md): 1 is
P5, without the one second; 2 is merged into P1, as no stop-the-world for
readers (short waits for a lock are fine); 3 is P6; 4 is P7, a failed
database stops, with deterministic transactions in P2; 5 is P8; 6 is P9;
7 is P10; 8 is P11, "Simple before optimal".
