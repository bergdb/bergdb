005-53. Investigate the startup distance on the fly
===================================================

Status: open. Kind: investigate. Created 2026-10-26.

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
