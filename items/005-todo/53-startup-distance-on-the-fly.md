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


Size and order
--------------

M. After 007-03's step 2 runs if they come first (the same databases), and
before the deadline (007-03, step 3), whose decrease it must handle. With
006-06.
