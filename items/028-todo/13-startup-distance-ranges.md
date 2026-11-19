028-13. Decide: the startup distance's two ranges disagree
==========================================================

Status: in progress (decided 2026-11-19: the builders' methods go; made on
the branch `028-13-startup-distance-setter`). Kind: Decide. Frans: decided
(2026-11-19, 11:06 and 11:10).
Created 2026-11-14 by Frans Lundberg.

What: the Core API sets the startup distance in two places, with
different ranges and different handling of a value outside them:

* `DbBuilder.startupDistance(int)`, at make or open: 10 bytes to 10^9,
  a value outside refused with `IllegalArgumentException` (above 10^9
  since 028-12).
* `Db.setStartupDistance(int)`, on a running database: a negative value
  refused; any other value clamped to 400,000 to 10^9 bytes (twice
  `RecoverableStream.META_BLOCK_DISTANCE` to 10^9), and the clamped value
  set, with no exception (since 005-53).

So 100 kB is taken by the builder and raised to 400 kB by the setter, and
2^31 - 1 is refused by the builder and lowered to 10^9 by the setter. Both
are documented; nothing is wrong today. The Pub API takes 5 to 1,000 MB.

Why: one rule is easier to learn and to keep; the Core API's setters may
be reviewed with 2026.6's stable format (026-12).

Frans: decision; **decided 2026-11-19** (below, "The decision"): the
builders' methods go, which replaces the options A, B and C. The options
(coord-1114, 2026-11-14, 12:17):

* A. Leave both as they are, documented (chosen for now, Frans, 12:18).
* B. The setter refuses outside its range, as the builder does: one
  rule, but a running database's call changes behaviour; a caller that
  passes a large value to mean "as large as possible" gets an exception.
* C. The builder clamps as the setter does: one rule, but silent, and it
  undoes 028-12's choice.
* Also open in B and C: whether the builder's low end (10 bytes, which
  tests use, e.g. G4's 100 kB) should meet the setter's (400 kB).

Done when: Frans has chosen; for B or C the change, its tests and
`java/before-commit.sh` OK.

First step: list the callers of both in `java/` with the values they
pass.



The decision
------------

Frans, 2026-11-19, 11:06: "I am leaning towards removing the startup
distance from the builder. I don't think this is required. The default is
fine for a newly started database. A change is just one method call. Can
be run immediately after a database has started." And 11:10: "Yes, do
this. Start it. Yes, the Pub builder's method go too. I just wonder about
the range and the clamp. I like the range and the clamp. So we can test
the whole range."

So the startup distance is set only by the running database's setter, and
the builders' methods go. This replaces the options A, B and C above: with
one method there is one rule.

**The range and the clamp, as coord-1118 read them** (to be confirmed by
Frans): the Core setter clamps to the database's whole range, 10 bytes to
10^9, the range of the KV `/#i/-sd` that a start reads (028-15), so that
tests can use every value of it; it refuses a value below 1 with
`IllegalArgumentException`; the Pub setter keeps its user range, clamped to
5 to 1,000 MB.


What was made
-------------

On the branch `028-13-startup-distance-setter` (from `main` `a0a76461`),
by an agent of coord-1118, 2026-11-19.

* **Core.** `DbBuilder.startupDistance(int)`, its field and
  `DbBuilder.MAX_STARTUP_DISTANCE` removed. A new database is created with
  `Db.DEFAULT_STARTUP_DISTANCE`, 50 MB (the builder's default until now),
  which the creating start puts at `/#i/-sd` in the creation's second
  record, as before (028-15, 028-18). `Db.MIN_STARTUP_DISTANCE` (10) and
  `Db.MAX_STARTUP_DISTANCE` (10^9) are the range, package-private, as the
  builder's constant was; `Db.parseStartupDistance` checks the KV against
  them. `Db.setStartupDistance(int)` now:
  * refuses a value below 1 with `IllegalArgumentException`, changing
    nothing (until now a negative value was refused and 0 clamped);
  * clamps to 10 to 10^9 (until now 400,000 to 10^9);
  * **returns the value set, `int`**, the clamped value, now in force
    (it returned `void`); `getStartupDistance()` gives it too. A call
    whose clamped value is in force writes nothing, as before.
  Javadoc: the setter (the range, why the floor went, the return), the
  getter, `Db`'s class ("Opening a database"), `DbBuilder`'s class,
  `DbConstants.SD_KEY`.
* **Pub.** `DatabaseBuilder.startupDistanceInMb(int)` and its
  implementation in `DatabaseBuilderImp` removed; the clamp moved to
  `DatabaseImp.clampStartupDistanceInMb`. `Database.setStartupDistanceInMb`
  keeps its clamp to 5 to 1,000 MB and its `void` (the stable API;
  `getStartupDistanceInMb()` gives the value set). The builder's long
  Javadoc moved to the setter, whole: start time and its measurements, the
  heap (what must be kept, a start's heap, the catalogue's figures), the
  write buffer; a sentence added that a database for a small heap gets its
  small setting right after the start that creates it. `DatabaseBuilder`'s
  class Javadoc, its `cacheSizeInMb`, `Database`'s class Javadoc,
  `StartupInfo` and `package.html` now name the setter.
* **Callers.** Every caller in `java/` sets the distance with the setter
  right after `start()` (or after `DatabaseImp.createAndStart`), with the
  same value, so a small distance stays small. Where a test restarts a
  stream that it made, the restart's call is left out (the stream keeps
  the setting; the builder's value was ignored on a restart before), or
  kept where a helper starts both and the value is the same (a call with
  the setting in force writes nothing). Tests whose point was the builder
  were rewritten for the setter (below).

The user apps of 024-26 and 026-13 moved into `java/stress/apps/` with
028-23 while this was made (merged into the branch at 12:00). These called
the removed methods, and now set the distance after the start, the same
values (their copies in `items/` are records and stay as they were):

* `a2-churn/Churn.java` (its first value, until the run sets another, so
  that a restart does not undo the run's own setting),
  `a3-limits/WorstCase.java` (400,000), `a4-kill/Kill.java` (300,000),
  `a5-readers/Readers.java` (400,000), `a6-index-churn/IndexChurn.java`
  (`setStartupDistanceInMb(1)`, clamped to 5 MB as the builder's was);
* `b1-back-to-empty/BackToEmpty.java`, `b5-kill/KillEmpty.java`
  (300,000), `c2-slow-drive/SlowDrive.java` (its builder call dropped: it
  already called the setter after the start).

`lean/contract/bridge-faults.sh`: its faults level-0 and root-pointer
named TX 3 of the trace `tree-small/mixed-1`, the second transaction of
the workload; with the exporter's setting at TX 2 that is TX 4 (the top
node's time 4). No checker and no pinned statement changed.


The floor: is 400,000 needed?
-----------------------------

No. The floor of 400,000 was twice `RecoverableStream.META_BLOCK_DISTANCE`
(200 kB) since 2013 (005-53's history.md): the setter put a
dummy value of 200 kB to get a meta block with the new setting written,
and a smaller distance than twice that dummy made the call's own
transaction dominate the startup section. 028-15 removed the dummy. What
uses the distance today, checked in the code:

* The writer's take (`TransSeq.take`, `Db` at the commit): the deadline
  `streamLength - max(2 sd, span)` and the share; any value from 10 on
  works, and the builder gave 10 and up for years (tests at 10, 100,
  200, 300, 1,000 and 2,000 bytes; `LimitsTester` draws 10).
* Reclaim's pacing (`Reclaim.transactionCompleted`): an iteration begins
  after more than 2 sd of stream since the last one began; a small sd
  only makes iterations more frequent (tests at 2,000).
* `maintain()`'s least release and filler (`MAINTAIN_MIN_RELEASE`, M5)
  use the meta block distance, not sd.
* The start's search: the startup pos is read from the last record
  (`Db.readStartupPos`), the setting from its KV; neither depends on a
  floor.
* The meta block distance is fixed (200 kB) and has held no sd since
  028-15.

So nothing needs a floor above 10, the KV's own least (028-15).



Tests
-----

* Rewritten for the setter: `DbTester.testSetStartupDistanceClamped` (every
  value of 10, 11, 100, 2,000, 399,999, 400,000, 50 MB and 10^9 taken and
  returned, each a record; above 10^9 and 1 to 9 clamped, the clamped value
  returned, nothing written if in force; 0, -1 and `Integer.MIN_VALUE`
  refused, nothing written; the smallest kept over a restart and the
  database written and read at 10 bytes); `DbTesterJavadoc.
  testSetStartupDistanceRange` (was `testBuilderStartupDistanceLimit`);
  `DbTester.testStartInfoReportsEffectiveDistance`, `testStartupDistance1`
  and `2`, `testSetStartupDistanceInForceOrRefused`; `DatabaseBuilderImp`'s
  `testStartupDistance1` (50 MB by default, then 7) and `2` (the Pub clamp,
  1 to 5 MB, 5,000 to 1,000 MB); `LimitsTester` (its first setting by the
  setter, its arguments around the new clamp, the returned value checked);
  `DbTesterRestart`'s tests of the KV (the restarts that showed the builder
  ignored now start without a setting); `Reclaim`'s
  `testIterationsFollowTheStreamsStartupDistance` (both runs start the same
  way now).
* Changed because the setter's call is a record of its own after the
  creation: `CorruptStreamTester`'s seven found cases re-located in the new
  streams (the same kinds of damage, refused or failing a read as before;
  seeds changed in three: 729001 to 729020, 20766 to 20774, 20765 to 20769;
  each test's Javadoc names the new places); `DbTester.testStartupPos1` (the
  first record's startup pos is the setter's record); `DbTesterStream`'s
  two creation tests (the creation's setting is the default; the setter's
  record after the force checks); `Eviction.testLoweredBudgetAfterPinsFell`
  (550 transactions, from a sweep of 480 to 600: 490 to 520 and 550 reach
  the state); `ScenarioTester.scenario107` (100 kB, not 10 kB, so that the
  whole stream stays the startup section and `DagComparison`, which cannot
  follow stream pointers, works as before).
* `TraceExport` sets the run's sd right after the start: R(2) of a trace is
  the setter's record, and the workload begins at R(3) (027-02).


Log
---

2026-11-14. Registered by coord-1114 from 028-12's landing (Frans, 12:18:
"Yes" to "pick A today and register a 028 entry").
