005-53. Investigate the startup distance on the fly
===================================================

Status: done (2026-10-28: option E, decided by Frans and implemented with
005-52; see Outcome). Kind: investigate. Created 2026-10-26.

Found in [010-01](../010-principles/01-principles.md), 010-P6 ("No
interruption for changes"), and studied first as 010-03; registered at
Frans's request (2026-10-26: "Move 03 contents from 010 principles to a new
item in 005. This should be investigated properly. In a separate work
item."). The first study, the history from 2013 to today, is in
[53-startup-distance-on-the-fly/history.md](53-startup-distance-on-the-fly/history.md).


The issue
---------

The Pub API cannot change the startup distance of an existing database:
it is set when the database is created, and an existing database keeps
the one in its stream (`DatabaseBuilder.startupDistanceInMb`). That is a
deviation from 010-P6. The core can change it while the database runs,
since 2013-04: `Db.setStartupDistance`, with a dummy transaction of 200 kB,
offered only through JMX (`Jmx.DbMonitor`) and used only by tests and
manual tools (history, sections 1 and 5).

A large database needs a startup distance chosen for it, 200 to 1000 MB
(005-38), and fast restart (006-06) needs to lower it for a while. A
decrease is the hard part: once 007-03's deadline is built, a decrease
takes every transaction that the new d_h makes due in one long commit
(007-04, point 6), against 010-P1 and 010-P4. D4 is decided as B: the
setter lowers the distance in steps, each with its own transaction
([007-03](../007-bounds/03-plan.md)).


Questions
---------

1. The decrease, measured: today's setter on large databases (1000 to
   100 MB, 200 to 50 MB, from 007-03's step 2): the longest commit, the
   waits of readers and writers, and how long the startup section stays
   long. Then with D4's steps: what step size keeps every commit within
   010-P1's 20 ms?
2. The Pub API: options A to D of the history's last section (keep the
   deviation; `Database.setStartupDistanceInMb` returning a `Job`; the
   builder's value applied to an existing database by an explicit call;
   B now and C later). Which, and why?
3. `Reclaim.initialStartupDistance` (`Reclaim.java` lines 180 and 332):
   is it the builder's value or the stream's, and does it ignore later
   changes? If it is wrong, what does that do to reclaim? A fix, if so,
   gets an entry of its own.
4. T3 with a distance that changes (006-06, question 4); the overflow of
   2 × sd above 1,073 MB (007-04, point 5); whether a change of distance
   belongs in 010-P2's list of settings that change the stream's bytes.
5. The pattern shared with [005-52](52-cache-size-while-running.md): a
   setting that changes while the database runs and converges in bounded
   steps. One way for both?


Done when
---------

* A report in `53-startup-distance-on-the-fly/`, with the measurements of
  question 1 and answers to 2 to 5, and a recommendation among A to D.
* Frans has decided; the work it leads to is registered (here, in 007, or
  in an entry of its own).


First step
----------

Question 3, a reading of `Reclaim` and `Db`'s start: small, and it may be
a fault of its own. Then question 1's runs, in the background, on F53.


Question 3: Reclaim's startup distance
--------------------------------------

By Claude (Opus 5.5, Claude Code), 2026-10-27 (006-09, W6.1), a reading of
HEAD `a6cd234`. Answer: it is the builder's value, never the stream's, and
it ignores later changes. A fault of its own, small: it changes how often
reclaim runs, not what it may cut. Registered and fixed as
[005-61](61-reclaim-startup-distance.md) (2026-10-27).

What the code does:

* `Db`'s constructor sets `startupDistance` from the builder and then
  makes the `Reclaim` (`Db.java`, lines 244 and 265). `Reclaim`'s
  constructor copies `db.getStartupDistance()` into the final field
  `initialStartupDistance` (`Reclaim.java`, line 180).
* `Db.start` runs later: `recover()` reads the stream's last valid meta
  block, and `handleStartParams` sets `Db.startupDistance` to the meta
  block's value (`Db.java`, lines 686 and 689). So for an existing
  database `Db` uses the stream's distance, as `DatabaseBuilder`'s Javadoc
  says, but `Reclaim` keeps the builder's: the Pub API's default 50 MB, or
  whatever `startupDistanceInMb` the opener passed.
* `Db.setStartupDistance` changes `Db`'s field and the meta block, not
  `Reclaim`'s.
* `Reclaim` uses it in one place: an iteration starts only when the stream
  has grown by `2 × initialStartupDistance` since the last iteration
  started, and a quarter of the retain duration has passed
  (`transactionCompleted`, line 332; the class comment's first point).
* Nothing else reads the startup distance once at start; `Db`'s other use
  (line 2051) reads its live field.
* The pattern is in the 2017 code (`195cf88`: `Reclaim.java`, lines 87,
  188 and 262).

What it does to reclaim: only the spacing of iterations. Every cut is
guarded by live values, not by this field: the startup position must have
passed `pSafe` (`markSafePositions`, `pretruncateIfPossible`) and the last
valid meta block's transaction must be at or after `pCut`. So no wrong
cut and no lost data. But:

* Opened with a builder value larger than the stream's (say made at 5 MB,
  opened with the default 50 MB; or made at 50 MB, opened with 1000),
  iterations wait for 2 × the larger value of growth: the stream keeps
  far more than the retention needs, up to 2 GB more at 1000 MB.
* Opened with a smaller one (made at 1000 MB, as 005-38 suggests for a
  large database, and opened with the default), an iteration may start
  every 100 MB of growth instead of every 2000 MB, when the retention is
  short enough: more iterations, more rows waiting in the table for the
  startup position to pass them, and more rewriting.
* After a change of distance (`setStartupDistance`, D4's steps, 006-06's
  lowering), reclaim keeps the distance it was opened with.

The probe, [ReclaimDistanceProbe.java](53-startup-distance-on-the-fly/ReclaimDistanceProbe.java)
(core API, memory stream, retention 1 s, 6000 small puts per run), makes a
database at 2000 bytes and restarts it twice:

| Run | Db's distance | Reclaim's | Iterations | Stream kept after the last cut |
|---|---|---|---|---|
| Made with 2000 | 2000 | 2000 | 64 | 98,448 bytes |
| Restarted, builder 2000 | 2000 | 2000 | 65 | 123,064 bytes |
| Restarted, builder default | 2000 | 50,000,000 | 1 | 2,426,672 bytes |

With the default in the builder, reclaim nearly stops: one iteration
instead of 65, and 20 times the stream kept.

A fix, for an entry of its own (not made here): `transactionCompleted`
reads `Db`'s live distance (it holds the write lock, which guards that
field) instead of the copy made in the constructor. The spacing then
follows the stream's distance and every later change. A unit test: the
probe's third run, asserting that the iterations match the second's.


Size and order
--------------

M. After 007-03's step 2 runs if they come first (the same databases), and
before the deadline (007-03, step 3), whose decrease it must handle. With
006-06.


The Pub API after D4:B: options A to E
--------------------------------------

By Claude (Opus 5.5, Claude Code), 2026-10-28 (006-10, W4.2), a reading of
`main` at `b1111f4`, with D4:B in the core since `f89846d` (007-07, 10).
The evidence, code citations and numbers, is in
[53-startup-distance-on-the-fly/report.md](53-startup-distance-on-the-fly/report.md).
Questions 1, 4 and 5 are answered there too (its sections 2, 4 and 5); in
short: one call needs no steps, T3 holds for the deadline in force, the
2 × sd overflow cannot happen below the 1000 MB clamp, and the startup
distance and the cache size share one pattern (005-52).

**What every option starts from.** `Db.setStartupDistance(int)` clamps to
400 kB to 1000 MB and, under the write lock, sets the setting and commits
a transaction with a 200 kB value, so that a meta block (one every 200 kB
of stream, the startup distance at offset 40) records it. A start reads
the last valid meta block's value (`Db.handleStartParams`), so a restart
keeps it; and it must, as the setting decides which index nodes each
record takes: the bytes would otherwise depend on restarts (010-P2;
`DbTesterRestart.testSameStreamAfterDecreaseWithRestartsF` checks that
they do not). Since D4:B one call is enough:

* A decrease: the share follows the new setting at once, and the deadline
  comes down with the span of the section's transactions instead of
  jumping to the new 2 × sd. At 10M keys, 1000 to 100 MB and 200 to 50
  MB: the call's own record 3.3 to 5.4 MB, the largest record after it
  2.3 to 5.1 MB, the section below the new 2 sd after 0.6 to 0.7M puts
  (820 MB of stream) and 0.1M puts (234 MB), and at 1.04 to 1.10 sd after
  (007-07, 10.4). Without D4:B one record of 486 MB, or 87 MB; caller's
  steps of 10 MB, up to 54 MB (007-06). The section comes down only as
  the application commits: with no writes, nothing pays the debt (007-06,
  5.3).
* An increase: nothing becomes due; the commits write fewer index nodes
  until the section has grown to the new setting (1 to 4 MB: 1.02 times
  it, smaller records; 007-07, 10.1). It costs what a larger distance
  costs: a longer start, and more pinned memory, as the nodes changed
  since the startup position are never evicted (`DatabaseBuilder`'s
  `cacheSizeInMb` Javadoc).
* Replicas: the new value is in the stream's meta blocks, which a replica
  receives with the bytes; a replica started as the database keeps it.
  Nothing of its own (replication is experimental, 005-11).
* Reclaim follows the change at once (005-61).

### A. Keep the deviation

The Pub API stays as it is: `DatabaseBuilder.startupDistanceInMb` for a
new database, the stream's value for an existing one. The core and JMX
(`Jmx.DbMonitor.setStartupDistance`, registered only by manual tools)
change it.

* API: none. Javadoc: none; `Db.setStartupDistance`'s is already right.
* Gives: nothing to build or test.
* Costs: 010-P6 stays broken for Pub users. A database created at the
  default 50 MB that has grown to 10M keys and more cannot get the 200 to
  1000 MB that 005-38 advises (updates at 10M keys: 867, 524 and 190
  stream bytes a put at 50, 200 and 1000 MB; 007-07, 10.4), but by
  `((DatabaseImp) db).getDb()`, which is not API. Fast restart (006-06)
  has no Pub call to build on.
* Effort: none.

### B. `Job setStartupDistanceInMb(int)` (obsolete after D4:B)

As history.md proposed: a setter on `Database` that returns a `Job`, as
`deleteIndex` and `addReplica` do; "an increase finishes at once; a
decrease runs in D4's steps and the job is done when the startup section
is below the new d_h".

* Obsolete as written: D4's steps are gone; after one call the take does
  the work, with the application's commits. A `Job` is "a long-running
  job performed in the background" (`pub/util/Job`), and nothing would
  run in the background: the job would only watch the section, its
  `join()` would wait for the application's own writes, and on an idle
  database it would wait for ever (007-06, 5.3). To be a real job it
  would have to write the debt itself, in records of bounded size: that
  is 006-06's question 3 ("write D now"), new work against 010-P3 and P4,
  not this setter.
* Persistence, replicas, stopping, tests: as E, plus the job's status.
* Effort: S for the setter, M with a job that means something.

### C. The builder's value applies to an existing database (subsumed by E)

`DatabaseBuilder.startupDistanceInMb`, or a separate, explicit builder
call, changes an existing database's distance after `start()`.

* Changes what the builder promises ("Existing databases keep the
  startup distance stored in their stream"); in the implicit form, an
  application that always passes the default would lower older databases
  without knowing, so only an explicit form was ever acceptable.
* Subsumed by E: with E, an application that wants it writes one line
  after `start()`, `db.setStartupDistanceInMb(200)`, and with E's no-op
  for the value in force (below) that line costs nothing at the starts
  after the first. No second way to do the same thing (010-P10).
* Effort: S on top of E; not needed.

### D. B now, C later (falls with B)

B for the change at runtime, C as a convenience on top. Falls with B; C
is not needed with E.

### E. `void setStartupDistanceInMb(int)` and `int getStartupDistanceInMb()` (new; recommended)

A plain setter and getter on `Database`, beside `setRetainDuration`, kept
in the stream as the setting is today.

* API, in `pub/Database`:

      /**
       * Sets the startup distance, the target size of the startup section:
       * the part of the stream that a start reads (bergdb 005-49). The value
       * is clamped as DatabaseBuilder.startupDistanceInMb() clamps it, to 5
       * to 1000 MB. The new setting is in force when the method returns: it
       * is written to the stream with a small transaction of the database's
       * own, so a restart keeps it, as it keeps the setting the database was
       * created with; a call with the setting in force writes nothing.
       *
       * The startup section follows the setting as transactions are
       * committed: after a decrease, each commit writes more of the index,
       * in proportion to its size, and no commit writes the whole of it; the
       * section is near the new setting after stream of about 1.4 times the
       * index changed since the startup position (bergdb 007-06, 007-07).
       * Without commits it does not move. After an increase, commits write
       * less of the index until the section has grown to the setting. A
       * larger distance writes fewer bytes a put and starts more slowly.
       *
       * @throws IllegalDbStateException  if the database is stopping or
       *     stopped, and DbFailedException if it has failed, as a
       *     transaction does; the setting is then unchanged.
       */
      public void setStartupDistanceInMb(int startupDistanceInMb);

      /** Returns the startup distance setting in MB (rounded), the target,
       *  not the section's present length. */
      public int getStartupDistanceInMb();

* The code: `DatabaseImp` clamps and calls `Db.setStartupDistance`;
  `getStartupDistanceInMb` divides `Db.getStartupDistance()`. In
  `Db.setStartupDistance`, two small changes: return at once when the
  value is the one in force (no 200 kB transaction), and check the state
  before the setting changes, so that a refused call changes nothing
  (today the field changes first; 1.2 of the report). No new core method
  (010-P12), no new setting (010-P10), no format change.
* Persistence: in the stream, as today (meta blocks); the builder's value
  stays for new databases only, and its `@param` ("between 5 and 100")
  says 5 to 1000.
* A stopping or failed database: the call throws as a transaction does
  and changes nothing. Replicas: as above.
* Tests: through `Database`, in memory: a decrease and an increase, each
  followed by commits, the section near the setting (the core's D4:B
  tests already check the take, 007-07, 10.2); a restart, with the
  builder at its default, keeps the new value; the clamp (1 gives 5,
  5000 gives 1000); a call with the value in force leaves the stream's
  length unchanged; a call after `stop()` throws and a restart shows the
  old value. StreamDigest unchanged (none of its configurations calls the
  setter). No Lean.
* Docs: `releases/next.md`, 010-01's P6 ("Where BergDB stands"), the
  builder's Javadoc.
* Gives: 010-P6 for the startup distance, with one call; the Pub form of
  Frans's two meanings (005-49): the setter sets the target, the take
  holds the actual near it.
* Costs: each call that changes the value writes a 200 kB value and, after
  a decrease at 10M keys, a record of 3.3 to 5.4 MB (whether the value
  should earn that share is 007-07's open point, 10.5; not a blocker).
  Fast restart wants to know when the section is short; this option
  leaves that to 006-06.
* Effort: S, about half a day with `before-commit.sh`.

### Recommendation

E. D4:B turned the hard part, the decrease, into the take's ordinary work,
so the Pub method needs no steps and no job: a setter that returns when
the setting is in the stream, as `setRetainDuration` returns when it is in
force. B's job would do nothing and might never finish; C is one line
with E; A leaves P6 broken for the setting that matters most for large
databases. Decide it with 005-52, as one pattern for a setting changed
while running (the report, section 4), and implement the two in one
commit.


Questions for Frans
-------------------

1. Which option? Recommended: E, `setStartupDistanceInMb` and
   `getStartupDistanceInMb` on `Database`, kept in the stream.
2. A call with the value in force writes nothing (no 200 kB transaction),
   so an application may call it after every start? Recommended: yes.
3. A getter for the actual startup distance (the section's length), for
   fast restart? Recommended: not now; with 006-06.
4. The 200 kB value's share (007-07, 10.5)? Recommended: count it, as
   now; it does not block E.
5. Decide and implement together with 005-52, one pattern? Recommended:
   yes, one commit.


Decision
--------

Frans, 2026-10-28, 12:32: "53 and 52. Yes, do this as recommended.", and
the smaller questions "as recommended". So: E; a call with the value in
force writes nothing; no getter for the actual startup distance now (with
006-06); the 200 kB value keeps counting toward its record's share, as
now; done together with 005-52, in one commit.


Outcome
-------

2026-10-28, by Claude (Opus 5.5, Claude Code), for 006-10, in a clone on
`8b37ad1`, together with [005-52](52-cache-size-while-running.md), whose
Outcome has its half; the code is one commit, `fd8f513`.

* The API, in `pub/Database`, beside the retain duration:
  `void setStartupDistanceInMb(int)` and `int getStartupDistanceInMb()`.
  `DatabaseImp` clamps as the builder does (5 to 1000 MB; the clamp is
  now one static method of `DatabaseBuilderImp` that both use) and calls
  `Db.setStartupDistance`; the getter rounds `Db.getStartupDistance()` to
  MB. No new core method (010-P12), no new setting, no format change. The
  Javadoc says what E's text says, and the pattern: a setting that
  changes the stream's bytes is kept in the stream (P2), one that does not
  lasts for the run.
* `Db.setStartupDistance`, two changes: under the write lock it checks
  the state first (`assertDbStateIsActive`), then returns at once when the
  clamped value is the one in force; and if the transaction is refused,
  or fails the database, it puts the setting and the in-memory meta
  block's value back before it rethrows. So a refused call changes
  nothing; until now the setting changed before `execute` checked the
  state (report, 1.2).
* A stopped or stopping database: the call throws as a transaction does,
  `IllegalDbStateException` (`DbStoppingException` while stopping) or
  `DbFailedException`, also for the value in force, and the setting stays.
  The getter works after `stop()`.
* `DatabaseBuilder.startupDistanceInMb`'s Javadoc: "between 5 and 1000"
  (it said 100), and that `Database.setStartupDistanceInMb` changes an
  existing database's distance, which the stream keeps.
* The tests:
  * `PubTester.testSetStartupDistanceInMb` (unit): in force at once (the
    getter and `Db`'s value, the stream grown by the call's 200 kB); the
    same value again appends nothing (the stream's length unchanged); 1
    gives 5 and 5000 gives 1000; after `stop()` a call throws
    `IllegalDbStateException` and the setting stays 20; a restart whose
    builder passes the default (50) has 20.
  * `PubTester.testDecreaseOfStartupDistanceInMbF` (f, D4:B's small
    check): 50 MB, 15,000 transactions of 20 small puts over a million
    keys (a section of about 22 MB), lowered to 5 MB, then 300 commits. No
    record from the call on is more than a third of what the records wrote
    until they were back near their size before the call (largest about
    3.0 MB of about 16 MB, over 10 records). With the deadline at twice
    the new setting at once (D4:B removed, a mutation for the check), one
    record took 9.4 MB of 17.0 MB and the test fails.
  * `DbTester.testSetStartupDistanceInForceOrRefused` (unit, core): the
    value in force writes nothing; a call after `stop()` throws and leaves
    the setting.
  * Mutations of the change, each in a copy: without the return for the
    value in force, `DbTester`'s and `PubTester`'s tests fail ("nothing
    written, expected 384, got 200616"; "the setting in force: nothing
    appended, expected 200616, got 400832"), as on the code before;
    without the state check first and the restore, both fail on the
    refused call ("Expected 1000000, got 3000000"; "the refused call
    changed the setting, expected 20, got 30").
* StreamDigest, `StreamDigest all` with main's compiled class (`8b37ad1`)
  against main's jar and the change's: "DIGESTS IDENTICAL (36 of 36)",
  and the change's digests are 007-07's `digest-patch.txt`: none of its
  configurations calls a setter, so nothing changes.
* Gates, on the change (`8b37ad1` and the code, identical in java/ to
  `fd8f513`), F53 with other sessions' runs about, nice 10:
  `before-commit.sh` "BEFORE COMMIT OK (103 s)" (1,069 unit tests, 77
  f-tests; deps.py: 9 packages, all as package.html allows);
  `level3.sh` (full) "LEVEL 3 OK" (conformance: 25 traces, TRACECHECK OK
  25, C-CUT 0 of 305); `level4.sh` (full) "LEVEL 4 OK" (EVICTION
  INVARIANCE OK in all 9; conformance: 45 traces, C-P and C-H 0 of 10,344
  transactions fail); `level2.sh quick` "LEVEL 2 OK" (14 traces,
  TRACECHECK OK).

Left: 006-06 (fast restart) wants to know when the section is short; a
getter for the actual startup distance is for it (question 3). The retain
duration shapes the stream's bytes and yet a restart takes the builder's
value (report, 1.2, the aside): not this entry's; its Javadoc does not say
so.

Files: [53-startup-distance-on-the-fly/](53-startup-distance-on-the-fly/):
`impl-gates.txt` (the gates' summary lines), `impl-digest-base.txt` and
`impl-digest-change.txt` (StreamDigest's output, main and the change).
