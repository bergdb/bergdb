033-bugs
========

Created 2026-11-20 by Frans Lundberg. Status: open.

The register of released bugs: faults in the code of a published release
of BergDB, one entry each, with a stable ID `RB-nnn`. For judging
BergDB's stability over its releases, how buggy or bug-free it is; later
also for users. It starts with release 2026.5, the first public release
of the 2026 era (Frans, 2026-11-20).


Rules
=====

Decided by Frans, 2026-11-20.

* **A released bug** is a fault in the code of a published release: the
  release does what its notes, its Javadoc or its contract say it does
  not, such as a lost or wrong value, a failed database, or a refusal it
  should not make. Not a released bug: performance, the wording of a
  document, a fault only in the tests or the harnesses. A fault known at
  the release, named in its Known issues, is a released bug too.
* **IDs** are `RB-001`, `RB-002`, ..., in the order of registration;
  never reused. Cite as `RB-001` (in code comments `bergdb RB-001`).
* **Severity**, the worst a user can meet:
  * S1: data lost or wrong;
  * S2: the database fails or will not start;
  * S3: a call fails or refuses wrongly, with no damage;
  * S4: minor.
* **An entry** has: what a user sees (one or two sentences, for users);
  severity; the releases with the bug and the release that fixes it;
  when and how it was found (review, AI-user apps, the C port, a harness,
  a proof, a user); known at the release or not; the fix's commits; the
  item with the details.
* **Theoretical faults count** (Frans, 2026-11-24): a fault that can be
  considered a bug is registered even when it is only possible in theory
  and was never seen; its severity says how little it matters. The kind
  and number of bugs found say how good a release is and what kinds of
  bugs the work finds.
* **Kept current:** the commit that registers a fault of a released
  version (an entry in 028, a release item's subitem) or that fixes one
  adds or updates its entry here. A release's steps check this register
  before its tag (026's release steps), and its notes name the released
  bugs it fixes by ID.
* **Where they are published** (Frans, 2026-11-24): each release's notes
  list the released bugs known in it at the release, under its known
  issues, and the ones it fixes. A bug found after a release goes into
  the section "After the release" at the end of its notes (Frans,
  2026-11-24, 12:58): the text above the section stays as published on
  the release day; the section's first line is "Added after YYYY-MM-DD;
  the notes above are as published on that day.", then dated bullets,
  oldest first, appended only, never edited. A bug's bullet is one or two
  lines: its ID, severity, state and a link to this register, the
  authority on the bugs. The latest release's notes get a bullet for each
  bug found after it (the repository's file and the GitHub release's
  page, set again when a bullet is added); an older release that has the
  bug gets one pointer bullet to this register with the IDs. A
  correction of a fact in the notes is a dated erratum in the same
  section ("Corrected: ... reads ...; it should read ..."), not an edit
  of the text above. README.md and bergdb.org list no known issues; they
  point to the notes and to this register, which lists them all.


Counts
======

Released bugs by the release they were found in, counting each bug once,
in the first published release that has it. Updated with each entry.

| Release | S1 | S2 | S3 | S4 | All |
|---|---|---|---|---|---|
| 2026.5 | 0 | 2 | 0 | 4 | 6 |
| 2026.6 | 0 | 0 | 0 | 0 | 0 |

Released bugs in each release, each bug counted in every published
release that has it (2026.6 has RB-005 and RB-006, first found in
2026.5):

| Release | S1 | S2 | S3 | S4 | All | IDs |
|---|---|---|---|---|---|---|
| 2026.5 | 0 | 2 | 0 | 4 | 6 | RB-001 to RB-006 |
| 2026.6 | 0 | 0 | 0 | 2 | 2 | RB-005, RB-006 |


Released bugs
=============

RB-001. A value transformation that throws or passes 8 MiB fails the database
------------------------------------------------------------------------------

* **What a user sees:** a value transformation (Core API) that throws, or
  whose result is over 8 MiB, fails the database instead of refusing the
  transaction. A restart has the state before that transaction; nothing
  committed is lost.
* **Severity:** S2.
* **Releases:** 2026.5 (and 2026.4 and before); fixed in 2026.6.
* **Found:** before release 2026.5 (024-24, QL6; 015-51); known at the
  release, named in 2026.5's Known issues. Counted a bug by Frans,
  2026-11-20.
* **Fix:** 026-06 (`a5c67ba1`, `11a9ef81`), 2026-11-13: the transaction
  is refused with a `DbException` and the database goes on (010-04, R5).


RB-002. A key transformation that throws fails the database
-----------------------------------------------------------

* **What a user sees:** a key transformation (Core API) that throws a
  `RuntimeException` fails the database instead of refusing the
  transaction. A restart has the state before that transaction.
* **Severity:** S2.
* **Releases:** 2026.5; fixed in 2026.6.
* **Found:** 2026-11-13, by the review of the code while fixing RB-001
  (026-06, Q2); not known at the release.
* **Fix:** 026-06 (`b159cd30`), 2026-11-13: refused with a
  `DbException`, as for RB-001.


RB-003. The Core API's Javadoc does not say that a new database is durable only at its first sync
---------------------------------------------------------------------------------------------------

* **What a user sees:** with the Core API (`bergdb.core.Db`), a crash after
  the start that creates a database returned, and before a sync, can make
  the next start throw `DatabaseNotCreatedException`; the Javadoc of
  `Db.start()` and of the exception spoke only of a crash while the
  database was created. A Core user who needs a new database to survive a
  crash or a restart calls `Db.sync(SyncLevel.ORDINARY)` after
  `Db.start()`. The Pub API syncs the creation in its start and is not
  affected. Nothing committed is lost: the database holds no data.
* **Severity:** S4 (unclear documentation of the Core API; Frans,
  2026-11-20).
* **Releases:** 2026.5 (and before); fixed in 2026.6.
* **Found:** 2026-11-20, by 028-35 (the user app KillEmpty under kills);
  not known at the release.
* **Fix:** 028-40, 2026-11-20: the Javadoc only; the behaviour is
  unchanged (Frans, 2026-11-20).


RB-004. Databases created at once around midnight may get a wrong date in created.txt
-------------------------------------------------------------------------------------

* **What a user sees:** databases created at the same time by threads of
  one JVM, at least one of them with the Core API, may get a wrong
  creation date in their `created.txt` if the date changes while they are
  created. `created.txt` is a text for people; BergDB does not read the
  date. No data, index or stream byte is affected. Possible in theory
  only: never seen, and a check with 8 threads of 5,000 calls each gave
  no wrong date.
* **Severity:** S4.
* **Releases:** 2026.5 (and before, since the code of 2017); fixed in
  2026.6.
* **Found:** 2026-11-16, by 028-07's review of the code (why a start
  held the lock of the class `DatabaseImp`): `Util.today()` formatted
  with a shared `SimpleDateFormat`, which is not thread-safe; the lock
  ordered the Pub API's starts, not the Core's. Not known at the release.
  Registered 2026-11-24, after release 2026.6 (Frans); named in 2026.6's
  notes, in the section After the release.
* **Fix:** 028-07 (`72e8de5d`), 2026-11-16: `Util.today()` and
  `Util.dateAndTime()` format with thread-safe `DateTimeFormatter`s.


RB-005. The count of the index nodes a transaction makes dirty is short for a key transformed to a longer key
------------------------------------------------------------------------------------------------------------

* **What a user sees:** nothing within a transaction's limits. Db's
  check of the index nodes a transaction can make dirty (005-31), which
  keeps a transaction's nodes within a record, counts a key with a key
  transformation by the segments of the key as given; a key transformed
  to one of more segments can make more nodes dirty than counted (46 for
  39 in a test at node size 8). Within `execute()`'s limits, L1 to L5, a
  transaction's nodes stay within a record by a separate bound (TP26,
  stated in the Lean model, not proved; the least margin 0.7 %, at node
  size 8), so the short count changes nothing. Were a transaction's nodes
  to pass a record's room, they would never be taken into a record, and
  the database's startup would grow without end (bounded startup lost);
  nothing lost, the database goes on.
* **Severity:** S4 (possible in theory only: out of reach within the
  limits, by a stated bound).
* **Releases:** 2026.5 and 2026.6 (and before); fixed on `main` for
  2026.7. Named in the section After the release of 2026.6's notes and
  of 2026.5's.
* **Found:** 2026-11-24, by 028-45's test (`DbTesterDirtyCount`), from
  030-39's finding F7; not known at the releases.
* **Fix:** 028-50 (`33193b20`), 2026-11-24, option A of 028-45 (Frans):
  a transaction with a key transformation is counted after its key
  transformations, with the keys they gave, as a transaction without one
  is; one over the limit is refused before its go point, its keys as
  written given back, and the database goes on. Fixed on `main` for
  2026.7.


RB-006. maintain() stops beginning reclaim iterations after some cuts
---------------------------------------------------------------------

* **What a user sees:** with a finite retain duration, calls of
  `maintain()` (the Pub's `Database.maintain()`, the Core's
  `Db.maintain()`) begin no reclaim iteration, after some cuts, until
  the application has written about twice the startup distance since
  the last one began, though the Javadoc says they begin iterations by
  the clock, without that growth. So a database written slowly keeps up
  to about twice the startup distance of stream (about 100 MB at the
  Pub's default of 50 MB), not the stream of a few retain durations; and
  a database emptied after such a cut, then not written to, keeps the
  deleted data's stream (up to about twice the startup distance) for
  good, though the Javadoc says the calls bring it to within about
  400 kB of a fresh one's. It comes after the
  cut of an iteration that began within 400 kB of its cut point: the
  first iteration, or one that began a quarter of the retain duration
  after an iteration with nothing to cut, in a database that writes
  less than 400 kB in that time. Disk space only: no value lost or
  wrong, the database goes on, and the commits' own rule gives the
  space back after that growth.
* **Severity:** S4.
* **Releases:** 2026.5 (where `maintain()` came, 024-32) and 2026.6;
  fixed on `main` for 2026.7.
* **Found:** 2026-11-24, by 028-47's study of commits that reclaim by
  the clock (finding F1, `SlowDriveProbe`); not known at the releases.
* **Fix:** 028-51 (`68386bc6`), 2026-11-24: `maintain()`'s M1 begins
  an iteration also when the cut of the next one would release 400 kB:
  the stream written since reclaim last stored its table.


Log
===

2026-11-20. Created the item, with its rules (Frans), from release 2026.5.
Registered RB-001 and RB-002, both fixed by 026-06.

2026-11-20. RB-003 registered (028-40), S4.

2026-11-23. Checked for release 2026.6 (026-27, step 8): the 67 commits
of `git log release-2026.5..main` that change `java/src` read for fixes
of faults that 2026.5 has. RB-001 to RB-003 are the only ones; no new
entry, and the counts agree. The other fixes are not released bugs:
028-09 and 028-14 (a damaged stream; 2026.5's Javadoc calls the
detection of damage a best effort), 028-10 (`Db.StartParams`, internal
by 2026.5's Javadoc, "used for testing"), 028-16 and 028-38 (reachable
only from BergDB's own tests), 028-07 (starts that waited for each
other's sync, a cost; its race of `SimpleDateFormat` could only
give a wrong date in created.txt, a text for people, when starts not
ordered by the lock formatted it at once at midnight; never seen)
and 028-12 (the builder's startup distance up to 2^31 - 1: a corner of
the bound on startup, a cost); 028-17, 028-21 and 028-26 fix faults of
code that 2026.5 does not have, and 026-05's pending cut (`4b4999aa`)
was reached only with 026-05's steps and delayed cuts, a cost.

2026-11-24. RB-004 registered (028-07's date race), S4, after release
2026.6 (Frans): a fault possible in theory only, never seen, is
registered too (Rules). 2026.6 fixes RB-001 to RB-004.

2026-11-24. RB-005 registered (028-45), S4: the count of a key with a key
transformation is short; possible in theory only. Not fixed.

2026-11-24. After a review of release 2026.6: RB-001 to RB-003 say
"fixed in 2026.6", as RB-004 does, now that 2026.6 is released.

2026-11-24. The rule of where released bugs are published (Frans): in
each release's notes, not in README.md or on bergdb.org. RB-005 named in
2026.6's notes (repository and GitHub release); its fix chosen (A,
028-50). RB-004 was named in 2026.6's notes as a fixed bug earlier the
same day. Checked: no other fault of a released version was registered
on 2026-11-24 (028-01, 028-48: costs; 028-44, 028-46, 028-52: tests and
gates; the review's stale Javadoc texts: wording); 028-51 decides
whether `maintain()`'s stall (028-47, F1) is one.
Whether such a bug is also added to the notes of older releases
(2026.5's lack RB-002 to RB-005) is for Frans.

2026-11-24. Counts: a row for 2026.6, and a second table of the bugs in
each release (Frans).

2026-11-24. RB-005 fixed on `main` for 2026.7 by 028-50 (`33193b20`),
Frans's option A of 028-45.

2026-11-24. The notes' section "After the release" (Frans, 12:58): the
rule of where released bugs are published says how the notes are
updated after their release. 2026.6's notes are as published on the
release day above the section, which holds RB-004, RB-005 and the
review's three corrections as errata; 2026.5's section points here for
RB-002 to RB-005, found after it (RB-001 was known at its release), so
the older release's notes are decided too.

2026-11-24. RB-006 registered and fixed on `main` (028-51), S4:
`maintain()`'s M1 stopped beginning iterations after a cut of an
iteration that began within 400 kB of its cut point (028-47, F1); 028-51
found that it breaks what the Javadoc of `maintain()` promises. Named in
the section "After the release" of 2026.6's and 2026.5's notes and in
`releases/next.md`; counts updated.
