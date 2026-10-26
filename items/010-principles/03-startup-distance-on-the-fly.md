010-03. Startup distance on the fly
===================================

Created 2026-10-26 by Claude (Opus 5.5, Claude Code) for Frans Lundberg, at
his request: "On-the-fly changes to startup distance used to be supported in
the 2012 era. Have a look at this with a subagent so it does not block our
discussion."

How the startup distance could be changed while the database runs, from
2012 to 2017, and how that compares with today. For P6 in
[01-principles.md](01-principles.md). Only reading; nothing else was
changed.


Summary
-------

* The change on the fly came in April 2013, not in 2012. In 2012 and until
  2013-04-08 the distance was a builder setting that "must be set same
  value in startup when started up again!".
* From 2013-04-09 the core could change it while the database ran:
  `Db.setStartupDistance`, with a dummy transaction. It was offered to
  operators through a JMX MBean, `Jmx.DbMonitorMBean.setStartupDistance`,
  which manual test tools registered.
* It was never in the Pub API. No Pub method to change the distance of a
  running or an existing database was found in the history from 2013-06-06
  to 2017-08-01. The Pub builder setting (2015-07-31) acts on new
  databases only; an existing database has always kept the value in its
  stream.
* So nothing public disappeared. The core setter and the JMX MBean are
  still in the code today, unchanged since 2017. The 2026 work only
  documented the existing behaviour: "Existing databases keep the startup
  distance stored in their stream" (commit 2bd52c0, 2026-10-14).


Sources
-------

* `doc/`, `log.md`: f1 `a/007-bergdb-261012/bergdb/`, Frans's notes and
  log.
* Old Git: the bundle f1 `a/007-bergdb-261012/bergdb-git.bundle`, read in
  the clone `java/build/props-006-02/orig-git` (2013-06-06 to 2017-08-01,
  branches `main` and `map-cache-1707`). Searched with `git log -S` and
  `-G` for `setStartupDistance`, `startupDistance` and `StartupDistance`,
  over all files and over `pub/` and `pubimp/` only.
* This repo: `java/src`, `java/src-dev`, items 006-06, 007-03, 007-04.


1. A public way, then
---------------------

Before Git, the notes:

* 2013-01, `doc/2013/2013-01-notes.txt` lines 39-48: "startupDistance
  [...] is needed by DB.start() before the database has been started
  really. Thus it cannot be stored as an ordinary database entry. Instead,
  it is stored in the meta block (see db.RecoverableStream). We must
  carefully consider whether changing startupDistance is allowed. It would
  be nice to be able to increase it if necessary. Decreasing it seems less
  important."
* 2013-04-08, `doc/2013/2013-04-notes.txt` lines 123-135, "Current status,
  130408": "Set with DB.Builder.startupDistance(int). Not currently exposed
  to Pub API. DB field: private final int startupDistance." and "Note,
  currently must be set same value in startup when started up again! A
  larger startupDistance would work, I supposed. But a short one would not
  when a db is restarted."
* The same file, line 199, "To do": "Implement manual startupDistance
  changes (expose to Jmx)."
* `log.md` line 3169, 130409: "startupDistance that can change while
  database is running. DB.setStartupDistance()." Line 3161, 130410: "DONE!
  Automatic tests of DB.setStartupDistance()."
* `doc/years.txt` line 56, under 2013: "Startup distance can change while
  db is running."

In Git:

* The JMX MBean is in the first commit, 76c4792 (2013-06-06, "First commit
  of new GIT repository, just before release 2013.1.130606"),
  `KissDB/src/kissdb/core/Jmx.java` lines 37 and 129-130:
  `public void setStartupDistance(int newDistance);` in `DbMonitorMBean`,
  which calls `db.setStartupDistance(newDistance)`. The class comment:
  "MBeans used to monitor and control a DB instance." It registers as
  `bergdb.core.Db:type=Jmx.DBMonitor`. Only test and manual tools register
  it (`test.Concurrency`, `test.big.Huge`, `LoadA`, later
  `test.manual.Interactive`, which reaches the core through
  `((DatabaseImp) database).getDb()`). It is still there at the last old
  commit, 49aa48d (2017-08-01), and today.
* The Pub API: `git log -S setStartupDistance -- '*/pub/*' '*/pubimp/*'`
  finds nothing. In 2013 the Pub `Database` had `setRetainDuration`,
  `indexBuilder`, `deleteIndex`, `addReplica` and `removeReplica`, but
  nothing for the startup distance, and the Pub builder had no startup
  distance either.
* b690311 (2015-07-31), "pub.DatabaseBuilder.startupDistanceInMb()
  added.", `bergdb/pub/DatabaseBuilder.java` lines 56-64: "Sests the
  startup distance to a non-default value. A small startup distance may
  decrease database startup time; while a larger startup distance may
  improve the overall database performance. For a low-end PC, a value of 5
  is reasonable, while a high-end server may use 50." f8bcb59 (the same
  day) added: "The value should be seen as a proposal, to the database. If
  the database considers the value too small or to high, it may clamp it
  to an internally permitted range." Nothing on existing databases.


2. How the core did it
----------------------

The value was stored in the meta block from the start of Git: 76c4792,
`KissDB/src/kissdb/storage/MetaBlock.java` line 22: "40 4 startupDistance
in bytes. Typically 10M (LE-first byte order)." It still is.

**2013-04 to 2013-10: increase and decrease handled apart.** The notes,
`doc/2013/2013-04-notes.txt`:

* Increase, lines 140-158: the in-memory distance changes only after the
  next meta block has reached the stream ("we must queue the change request
  somehow and wait until next meta block is written to stream").
* Decrease, lines 162-174: "The previous larger value of the
  startupDistance will exist for "upstarter" until next meta block is
  written to the stream. This is fine [...] A transaction should be written
  after the decrease to make sure the extra dirty nodes have been written
  before the startupDistance is written to metaBlock. For a large decrease,
  it could make sense to descrease startupDistance in steps of 1M and write
  a dummy transaction after each change. This is to avoid a huge
  transaction with dirty nodes."
* Line 196: "We must make sure to keep invariant metablock.startupDistance
  >= db.startupDistance."

The code, 76c4792 `KissDB/src/kissdb/core/Db.java` lines 320-378:
`setStartupDistance` refuses a change while an increase is pending
("An increase of startupDistance [...] has been requested but not
finalized"); `decreaseStartupDistance` sets the field, runs
`execute(Trans.builder().set(Db.DUMMY_KEY, new byte[0]).build())`, then
sets the meta block; `increaseStartupDistance` sets the meta block and
`newIncreasedStartupDistance`, which `Db` applies at line 1676 when a
transaction has written a meta block. The steps were not built; line 345:
"Note. Possibly, we could split decrease into many parts for large
decreases to avoid large transactions."

**From 2013-10-23: one method, one dummy transaction.** fc1a421
(2013-10-23), "Refactored Db.setStartupDistance() and related
startupDistance stuff. Much simpler now.", the same day as bfa7bf7
("Introduced StartupPos. Replaces direct use of Db.startupDistance.").
`bergdb/src/bergdb/core/Db.java` lines 355-386: the field, the meta block
and a dummy transaction whose value is `META_BLOCK_DISTANCE` bytes (200 kB),
so that the new value reaches a meta block at once; the distance is clamped
to [2 × 200 kB, 1000 MB]. The steps moved to the Javadoc: "If the startup
distance is reduced drastically, this method can cause a large transaction
to be run. It is recommended that the startup distance is reduced no more
than 10M for every call to this method. Call this method repeatedly to
reduce the startup distance more than 10M." This is the method of 2017
(49aa48d, lines 244-276) and of today.

**From 2015-08-09: the take spreads the debt.** e3f34c1 (2015-08-09), "New
algo for startupPos (sp) updates avoid huge transactions. Avoiding some
transactions getting an unfair load of index transactions to store.":
`TransSeq.take` takes dirty index nodes up to a node limit proportional to
the transaction (`valueCount * 4 + kvSize / 1024`, at least two
transactions). After a decrease the startup pos catches up over the
following transactions instead of in the dummy one. Its "TODO D." asks for
a factor "if startup pos is falling behind (with more than 2.0 *
startupDistance perhaps)".


3. The builder's value for an existing database
-----------------------------------------------

Ignored, in every version read:

* 76c4792 (2013-06): the constructor writes the builder's value into the
  in-memory meta block (line 247), `nodeStream.recover()` then copies the
  stream's last valid meta block over it (`RecoverableStream`, line 114,
  `setFromOtherMetaBlock`), and `start` reads it back: "if (!dbCreated) {
  this.startupDistance = nodeStream.getMetaBlock().getStartupDistance();"
  (lines 738-739).
* 49aa48d (2017): `handleStartParams` (line 508) sets
  `params.startupDistance = meta.getStartupDistance()`. The unit test
  `DbTesterRestart.dbShouldRememberStartupDistance1` (from ee3685d,
  2014-10-14, "Fixed restart / startupDistance bug.") restarts with a
  builder at its default and asserts the old 400 kB: "Db should remember
  startupDistance after restart of initial state database."
* The Pub builder of 2015 passes its value to the core builder
  (`DatabaseBuilderImp`, `dbBuilder.startupDistance(...)`), so it too acts
  on new databases only.


4. When the public way disappeared
----------------------------------

It did not: there was no Pub way to lose. The JMX setter and the core
setter are unchanged from 2017 to today (`git log -L` on today's
`Db.setStartupDistance` shows only 195cf88, 2026-10-14, "Import the 2017
BergDB source as the baseline"). The only 2026 change is documentation:
`git log -S "Existing databases keep"` gives 2bd52c0 (2026-10-14, "Add the
2026 work: fixes, reclaim, theory and Lean proofs"), which added to
`DatabaseBuilder.startupDistanceInMb`'s Javadoc: "The default is 50 [...].
Existing databases keep the startup distance stored in their stream." The
default changed from 20 to 50 MB on 2026-10-13 (`DatabaseBuilderImp` line
53). No note was found that decided against a Pub method; the 2013-01
notes leave it open ("Set in DB.Builder or after db.start()? Persistent or
not?", line 36).


5. Today
--------

* `Db.setStartupDistance` (`java/src/bergdb/core/Db.java` lines 319-351):
  as in 2013-10, under the write lock, one dummy transaction of 200 kB
  under `DbConstants.DUMMY_KEY`, clamped to [400 kB, 1000 MB], with the
  "no more than 10M for every call" Javadoc.
* Callers: no production code. `core.Jmx.DbMonitor` (the MBean, registered
  by the manual tools `Huge`, `LoadA`, `TransThroughput`, `Interactive`),
  the unit test `DbTester.testStartupDistance2` (line 1731), and the
  f-test `StartupDistanceTester` (`@Nano("f")`, in the f-test set:
  1000 kB, 400 kB, 2000 kB, 500 kB, then a restart).
* The take is still the 2015 one (`TransSeq.take`, node limit, "TODO D."),
  so a decrease today spreads its writes but leaves the startup section
  long until the take catches up; nothing tells the caller when.
* Not found elsewhere: `Reclaim` keeps `initialStartupDistance`, taken in
  the `Db` constructor from the builder (`Reclaim.java` line 180, before
  `start` reads the stream's value), and uses 2 × it to space its
  iterations (line 332). It ignores both the stream's value and later
  changes. 006-06's question 4 lists "reclaim's use of twice the startup
  distance"; this note does not check what it means for P2.

What a Pub method needs:

* An increase is cheap: the new value goes to a meta block with the dummy
  transaction, and the take only relaxes.
* A decrease meets the deadline of 007-03 step 3, once built: the dummy
  transaction "takes every transaction that the new d_h makes due, in one
  record, or a few at the record limit" (007-04, point 6), one long commit
  while the other writers and the readers of the stream's last file wait.
  That breaks P1 and P4. D4 is decided as B (Frans, 2026-10-26, "D4:B."):
  "`setStartupDistance` lowers the distance a little at a time, each step
  with its own transaction and the write lock released between them [...]
  and returns when the section is below the new d_h"
  ([007-bounds/03-plan.md](../007-bounds/03-plan.md)). This is the 2013
  note's "steps of 1M", built into the method instead of left to the
  caller.
* The step size comes from 007-03 step 2's runtime decrease (1000 to 100
  MB, 200 to 50 MB), not measured yet.
* The steps run in the call, or as work the call starts (P3 allows it),
  and each step's cost is bounded (P4). Each step costs a 200 kB dummy
  value today; a smaller dummy, or none when a real transaction writes the
  meta block soon enough, is a detail of the implementation.
* 006-06 (fast restart) wants the same call and a way to know when the
  section is short enough.


What restoring on-the-fly changes would take
--------------------------------------------

Options for Frans; not decided here. All of them need D4 (B) inside
`Db.setStartupDistance` first, and an answer for `Reclaim`'s fixed
`initialStartupDistance`.

* A. **Keep the deviation.** The core and JMX change it; the Pub API does
  not. Only the Javadoc of `Db.setStartupDistance` changes, with D4. Least
  work; P6 stays broken for Pub users.
* B. **`Database.setStartupDistanceInMb(int)` on a running database,
  returning a `Job`**, as `indexBuilder`, `deleteIndex` and `addReplica`
  do since 2013. An increase finishes at once; a decrease runs in D4's
  steps and the job is done when the startup section is below the new
  d_h. Fast restart (006-06) waits for the job. Closest to P6 and to the
  2013 Pub style.
* C. **The builder's value applies to an existing database**, after start,
  in the same steps. Changes what "Existing databases keep the startup
  distance stored in their stream" promises; an application that always
  passes the default (50) would change older databases without knowing.
  Possible only with an explicit form, such as a separate builder call.
* D. **B now, C later if wanted.** B gives the runtime change; C is a
  convenience on top of it.

To check in each case: tests for a decrease and an increase across a
restart (`StartupDistanceTester` extended), T3 with a distance that
changes (006-06, question 4), the overflow of 2 × sd above 1,073 MB
(007-04, point 5), and whether the change belongs in P2's list of
settings that change the bytes.
