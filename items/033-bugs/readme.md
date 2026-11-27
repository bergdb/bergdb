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
| 2026.5 | 0 | 3 | 2 | 8 | 13 |
| 2026.6 | 0 | 0 | 0 | 0 | 0 |

Released bugs in each release, each bug counted in every published
release that has it (2026.6 has RB-005 to RB-013, first found in
2026.5):

| Release | S1 | S2 | S3 | S4 | All | IDs |
|---|---|---|---|---|---|---|
| 2026.5 | 0 | 3 | 2 | 8 | 13 | RB-001 to RB-013 |
| 2026.6 | 0 | 1 | 2 | 6 | 9 | RB-005 to RB-013 |


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
  the stream written since reclaim last stored its table. In part
  (028-58, 2026-11-25): when less than 400 kB is written after the cut
  and the stretch before it is just below 400 kB, an emptied database
  on `main` keeps up to about 800 kB (783,472 bytes in 028-58's probe);
  the rest goes with RB-007's fix (031-03).


RB-007. maintain() keeps the stream written while an iteration waited for its cut
---------------------------------------------------------------------------------

* **What a user sees:** with a finite retain duration, a database that
  the application writes to and deletes from while a reclaim iteration
  runs or waits for its cut, and then no longer writes to, keeps the
  stream of those writes for good under calls of `maintain()` (the
  Pub's `Database.maintain()`, the Core's `Db.maintain()`), up to about
  twice the startup distance: the calls begin no iteration, though the
  Javadoc says that they bring a database that has been emptied to
  within about 400 kB of a fresh one's stream. It comes when that
  iteration began within 400 kB of its cut point, as RB-006 does (the
  first iteration, or one that began a quarter of the retain duration
  after an iteration with nothing to cut); RB-006's fix counts the
  writes made after the cut only. Disk space only: no value lost or
  wrong, the database goes on, and the commits' own rule gives the
  space back after about twice the startup distance of writes.
* **Severity:** S4.
* **Releases:** 2026.5 (where `maintain()` came, 024-32) and 2026.6;
  not fixed on `main`.
* **Found:** 2026-11-24, by 028-53 while it read `maintain()`'s rules
  against a database not written to (`HoleProbe`: 4,000 keys put and
  deleted, the first iteration done, 20,000 keys put and deleted before
  its cut, then 10 R of calls: 4.8 MB kept against 0.3 MB without the
  second writes, on 2026.5, 2026.6 and `main`); not known at the
  releases.
* **Fix:** none yet; 028-53's options A and B were not taken (Frans,
  2026-11-25); 031-03 looks for the fix.


RB-008. Db.getTrans refuses a large transaction's position just after a cut
---------------------------------------------------------------------------

* **What a user sees:** with the Core API, `Db.getTrans(tpos)` of a
  committed transaction of over 1 MiB, at a position that a get gave,
  throws `IllegalArgumentException` ("Not a position of a
  transaction"), for the transactions just after a reclaim cut when a
  transaction runs over the start of the first kept file (a file
  database) or 1 MB array (`MemoryStream`). Nothing is lost or changed,
  and the database goes on. The Pub API's
  `Connection.transactionInfo()` reads without that walk and is not
  affected.
* **Severity:** S3.
* **Releases:** 2026.5 (since `2858ed36`, 021-27, Q27-1) and 2026.6;
  fixed on `main` for 2026.7.
* **Found:** 2026-11-25, by `week.sh`'s soak of the user apps (Churn,
  a2, 024-26; seed 2078207, node size 30); not known at the releases.
* **Fix:** 028-55, 2026-11-25: the walk to a record's start begins at
  reclaim's cut, not at the stream's first position, when no meta
  block names a record's start.


RB-009. Db.getTrans can expire a kept large transaction while reclaim cuts the stream
-------------------------------------------------------------------------------------

* **What a user sees:** with the Core API, `Db.getTrans(tpos)` of a
  committed transaction of over 1 MiB, at a position that a get gave,
  can throw `LookupTimeNotAvailableException` though the transaction is
  kept, when reclaim cuts the stream during the call; a retry reads it
  (in 2026.5 and 2026.6 the retry may meet RB-008). Nothing is lost or
  changed, and the database goes on. The Pub API's
  `Connection.transactionInfo()` reads without that walk and is not
  affected.
* **Severity:** S3.
* **Releases:** 2026.5 (since `2858ed36`, 021-27, Q27-1) and 2026.6;
  fixed on `main` for 2026.7.
* **Found:** 2026-11-25, by Codex's review of 028-55, with a probe that
  holds the cut with latches; never seen in a run; not known at the
  releases.
* **Fix:** 028-56, 2026-11-25: the walk takes no record's start that a
  meta block names before reclaim's cut, and starts again when a cut
  removes what it reads while the position is kept.


RB-010. A stop or a crash during maintain() can leave its 200 kB filler live
----------------------------------------------------------------------------

* **What a user sees:** a stop or a crash between the two transactions
  of `maintain()`'s filler (M5) leaves `/#i/dreclaim/-fill.txt`, up to
  200 kB of zeros, live, though the Javadoc of `Database.maintain()`
  and of `Db` says that it is deleted at once. It stays live until a
  later call needs another filler, for good in a database not written
  to: each reclaim iteration rewrites it, and the Core's `getMany()`
  returns it and `getKvCount()` counts it. No value lost or wrong;
  alone it keeps the stream within 400 kB of a fresh one's (199,672
  bytes); with RB-007 an emptied database can keep more (856,176
  bytes against 284,416 without the stop).
* **Severity:** S4.
* **Releases:** 2026.5 (where `maintain()` came, 024-32) and 2026.6;
  not fixed on `main`.
* **Found:** 2026-11-25, by the review in 031-03 (section 9.2);
  confirmed by 028-59 with a stop, a copy of the stream and a killed
  JVM, on 2026.5, 2026.6 and `main`; not known at the releases.
* **Fix:** none yet; 031-03's design stores the filler as the table
  padded with spaces, one record with nothing to delete.


RB-011. An emptied file database keeps its last stream file under maintain()
----------------------------------------------------------------------------

* **What a user sees:** with a finite retain duration, a file database
  that held much stream and is then emptied keeps, under `maintain()`
  calls, the stream file that the first available position is in. That
  file's size was chosen as up to a quarter of the stream kept when it
  was made: 5 MB after 20 MB kept, 20 MB after 80 MB, up to 500 MB
  after 2 GB. The Javadoc of the Pub's `Database.maintain()` promises
  within about 400 kB of the size of a fresh database. Reclaim cuts the
  stream below 400 kB; `FileStream` drops only whole files and keeps
  its last one, which nothing fills. Disk space only: no value lost or
  wrong, and writes give the space back once they fill the file.
* **Severity:** S4.
* **Releases:** 2026.5 and 2026.6 (run on 2026.6; 2026.5 has the same
  rules of `FileStream`); fixed on `main` for 2026.7; 031-03 does not
  change it.
* **Found:** 2026-11-25, by 031-02's app hunt (F2: 10,400 kB kept
  where a fresh database keeps 904 bytes); its cause by 028-61; not
  known at the releases.
* **Fix:** 028-62, 2026-11-26, neither of its options J and S (Frans):
  the Javadoc of the Pub's `Database.maintain()` says that the calls
  bring the stream of an emptied database to within about 400 kB of a
  fresh one's stream, as the Core's `Db.maintain()` does, and nothing
  of files; `FileStream` gives a new file about a tenth of the stream
  that its files hold, not a quarter, and its Javadoc states that the
  disk can hold up to about one file more than the stream. RetainChurn's
  case: 400 kB on disk for 61 kB of stream, from 10,400 kB.


RB-012. After a kill on macOS, a zeroed tail over a meta block stops the start
-----------------------------------------------------------------------------

* **What a user sees:** after the writing process is killed during a
  large append on macOS (APFS), the last stream file can end in zeros,
  whole pages, within its length; where they cover a meta block's
  position, the next start throws `StreamFormatException` "Invalid
  magic bytes in stream: the stream is not a BergDB stream, or it is
  damaged; or an earlier release ... encrypted it", and the database
  does not start until a person cuts its last file. Where the zeros
  also run past a record's end, the file cut at the position that
  `Database`'s Javadoc names did not start either. The data that a sync
  returned for are there. The system makes the zeros (031-02's
  `ZeroTailProbe`, 1 in 150 kills with plain appends and forces);
  BergDB's part is the start's answer.
* **Severity:** S2.
* **Releases:** 2026.5 and 2026.6 (run on 2026.6; the same check of the
  meta block's magic since 2026.1, by the sources); fixed on `main` for
  2026.7.
* **Found:** 2026-11-25, by 031-02's app hunt (KillWriter: 3 in about
  9,500 kills); not known at the releases.
* **Fix:** part 1, 028-60 (`9cbf47f6`), 2026-11-25: a meta block of
  zero bytes is not valid, so zeros that begin inside the last record
  are recovered as a cut tail; zeros past a record's end get the
  documented refusal, "Bad transaction size in db stream, 0, spos P",
  and the file cut at P starts. Part 2, 028-60 (`ac33aa93`),
  2026-11-27 (Frans's
  decision of 2026-11-26: neither B1, B2 nor B3 as written): at the
  open, `FileStream` leaves a run of zero bytes of at most 8 MB at the
  end of its last file out of the stream, and its first append
  truncates the file where the run starts, forced, for every stream,
  on every operating system and file system; nothing above it changed,
  and the start recovers the stream as a cut tail. A start refused
  before it writes leaves the files as they were. 031-02's seed 63 now
  starts at the last synced transaction, with nothing done by hand. A
  longer run is left and taken as before; stale bytes that are not
  zero are 028-67.


RB-013. A stop between a transaction's record and reclaim's records after it changes the stream's bytes
-------------------------------------------------------------------------------------------------------

* **What a user sees:** after a `stop()` from another thread that lands
  between a transaction's record and the records of reclaim that follow
  it in the same commit, and a restart, reclaim's interrupted work (a
  begin, a step) goes on at the next commit at other positions, so the
  stream's bytes differ, from that record on, from those of a run
  without the stop, for the same accepted transactions. That is against
  010-01's P2 (the bytes a function of the accepted transactions, not of
  timing, threads or restarts) and the README's "The same transactions
  in the same order give the same bytes". No value lost or changed, and
  the database goes on. A crash at that point is not counted: a crash
  may leave a partial append, and the bytes after a crash are not
  promised (Frans, 2026-11-27, 16:41; 031-06's `p2-draft.md`).
* **Severity:** S4 (Frans, 2026-11-27).
* **Releases:** 2026.5 and 2026.6 (and before: 015-53, in 2026.3, made
  such a stopped call return instead of throwing `DbStoppingException`,
  and left the bytes as they were); fixed on `main` for 2026.7.
* **Found:** 2026-11-25, by 031-01's revision after Codex's review
  (028-54; `MidCallProbe`, a crash between a transaction's record and
  the begin of its iteration); the stop by the code (`Db.executeInner`)
  and by 031-05's probe on 031-04's prototype, whose commits maintain
  as `main` (031-05, section 7.1: crash and stop alike). Never seen by a
  user; not known at the releases. Registered 2026-11-27 (Frans, 17:12).
* **Fix:** 031-06, one record an action, merged into `main` on
  2026-11-27 (`5b88cc80`): a commit's record holds the maintenance that
  reclaim owes, so no record lies between a transaction's record and its
  maintenance, and a stop cannot land there (031-06, section 4.1 and
  `landing.md`, step 2: 27,720 interruptions at record boundaries, 0
  different). Fixed on `main` for 2026.7.


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

2026-11-24. RB-007 registered (028-53), S4: `maintain()`'s M1 counts
neither the application's writes made after the last iteration began
and before reclaim last stored its table, so a database emptied while
an iteration that began within 400 kB of its cut point waited for its
cut keeps that stream. Not fixed; 028-53 holds the options. Named in
the section "After the release" of 2026.6's and 2026.5's notes and in
`releases/next.md`; counts updated. The rewriting of live values that
028-53 was registered for breaks no promise (a cost) and is not
registered.

2026-11-25. RB-007's fix: 028-53's options A and B not taken (Frans);
031-03 looks for it.

2026-11-25. RB-008 registered and fixed on `main` (028-55), S3:
`Db.getTrans` refused a large transaction's position just after a cut,
in 2026.5 and 2026.6. Found by `week.sh`.

2026-11-25. RB-009 registered and fixed on `main` (028-56), S3: a cut
during `Db.getTrans`'s walk could expire a kept large transaction, in
2026.5 and 2026.6. Found by Codex's review of 028-55.

2026-11-25. RB-010 registered (028-59), S4: a stop or a crash during
`maintain()` can leave its filler live, in 2026.5 and 2026.6; not fixed.
RB-006's fix on `main` noted as partial (028-58).

2026-11-25. RB-011 registered (028-61), S4: an emptied file database
keeps its last stream file under `maintain()`, in 2026.5 and 2026.6;
not fixed (028-62).

2026-11-25. RB-012 registered (028-60), S2: after a kill on macOS, a
zeroed tail over a meta block stops the start, in 2026.5 and 2026.6;
fixed in part on `main`; the rest for Frans (028-60, B1 to B3).

2026-11-26. Frans confirmed RB-006's remaining part (031-03, section 9.1;
028-58) and RB-010 (031-03, section 9.2; 028-59) as released bugs, S4.
031-03's section 9.3 (a database not written to keeps several times its
live values) is a space cost, not a released bug: 028-65.

2026-11-26. RB-011 fixed on `main` for 2026.7 (028-62): the Pub's
`Database.maintain()` promises the 400 kB of the stream, and
`FileStream` gives a new file a tenth of the stream, not a quarter.

2026-11-27. RB-012 fixed on `main` for 2026.7 (028-60, part 2, as Frans
decided on 2026-11-26, after the removal of the internal encryption,
028-69): `FileStream`'s open leaves a tail of zeros of at most 8 MB at
the end of its last file out of the stream, and its first append cuts
them, so a kill's zeroed tail past a record's end starts too.

2026-11-27. RB-013 registered (028-54), S4 (Frans, 17:12): a stop
between a transaction's record and reclaim's records after it changes
the stream's bytes after a restart, in 2026.5 and 2026.6; the crash case
is not counted, as the bytes after a crash are not promised (Frans,
16:41). Fixed on `main` for 2026.7 by 031-06, one record an action
(`5b88cc80`). Named in the section "After the release" of 2026.6's and
2026.5's notes and in `releases/next.md`; counts updated.
