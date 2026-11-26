028-62. Decide: RB-011, an emptied file database keeps its last stream file
==========================================================================

Status: done. Kind: Decide. Frans: decided (2026-11-26): neither J
nor S; a tenth, and the Javadoc of the stream.
Created 2026-11-25 by Frans Lundberg.

What: RB-011 (033; found by 031-02, F2, its cause by 028-61). A file
database that held much stream and is then emptied keeps, under
`maintain()` calls, the stream file that the first available position
is in. Reclaim cuts the stream below 400 kB (61 kB of stream in
RetainChurn's seed 5), but `FileStream` drops only whole files and
keeps its last one, whose capacity it chose when the file was made, up
to a quarter of the stream kept then (a 20 MB file made while about 85
MB was kept); after the deletes only reclaim's records are appended,
about 1 MB, so the file never fills, every cut lands inside it, and the
disk keeps it whole: 10,400 kB on disk for 61 kB of stream, on `main`
and 2026.6 alike. 031-03's design does not change it.

Why: the Javadoc of the Pub's `Database.maintain()` promises "within
about 400 kB of the size of a fresh one"; the Core's `Db.maintain()`
says "of the stream", which holds. 027-13, section 4 ("the disk: 6 to
9 percent more than the stream kept") does not hold for a stream that
has shrunk.

Frans: decision, between:

* **J. The Javadoc.** The 400 kB are of the stream; a file database
  also keeps the rest of the file that holds the first available
  position, up to a quarter of the stream kept when that file was made
  (5 MB after 20 MB kept, 20 MB after 80 MB, up to 500 MB after 2 GB).
  No code. The promise becomes what the code does; RB-011 is closed as
  documented. 027-13, section 4 says the same.
* **S. The storage.** A file boundary after the first available
  position: for example, at a cut that leaves the stream kept far below
  the last file's capacity, `FileStream` ends that file at its next
  record and begins the next, of the size its rule gives; `maintain()`'s
  M1 counts the storage's bytes (from the storage's first position, not
  fp), so the calls begin an iteration whose cut passes the old file,
  which is then deleted. Not designed or measured (028-61, section 3);
  to check: whether a start accepts a file that is not the last and is
  shorter than its capacity. It changes how the files are laid out,
  not the stream's bytes.

Recommendation, lead-1125: S, if a design of it stays small (a few
rules in `FileStream` and one count in M1), as the promise of a return
to empty is what `maintain()` is for (Frans, 2026-11-25: the database's
return to empty is wanted); else J, with the bound written.

Done when: Frans's choice; with J, the Javadoc of `Database.maintain()`
and 027-13, section 4 corrected; with S, a design and a fix with a
test that fails before it, `java/before-commit.sh` printing `BEFORE
COMMIT OK`, RetainChurn's case at about 400 kB of disk over a fresh
database's.

First step: 028-61, sections 2 and 3; `FileStream`'s rule for a new
file's capacity and its deletion of whole files.


Decision
--------

Frans decided on 2026-11-26: neither J nor S as written. Instead:

1. `FileStream` gives a new file about a tenth of the stream kept, not
   a quarter (`determineFileSizeIndex`).
2. No promise about the disk's size in the Pub API: the sentence of
   `Database.maintain()`'s Javadoc that the calls bring an emptied
   database "to within about 400 kB of the size of a fresh one" becomes
   a statement of the stream, as the Core's `Db.maintain()` says, with
   nothing about files.
3. `FileStream`'s Javadoc states the low-level facts: files are deleted
   whole, a new file gets about a tenth of the stream kept, so the disk
   can hold up to about one file more than the stream; and the backup
   property that it keeps: files are only appended to and deleted whole
   from the oldest, so a copy of the files in order is a backup, said
   precisely, from the code.
4. 027-13, section 4 (the disk) and 027-14 (storage) corrected.
5. RB-011 fixed in 2026.7, by the documentation and the tenth.

Rejected: a copy and swap of files within the storage, for its
file-system complexity and as it would break the backup property.


Result
------

Done 2026-11-26 by an agent of lead-1126, on the branch `028-62` of a
clone of `main` at `8d86234b`.

### 1. The change

* `FileStream.determineFileSizeIndex`: a tenth of the stream that the
  files hold (`streamSize / 10`), from the first file's start to the
  length: 200 kB files below 10 MB, 1 MB from 10 MB, 5 MB from 50 MB,
  20 MB from 200 MB. The rest of the rule as before: a larger size
  begins at a length that is a multiple of the next larger size, a
  smaller one at once.
* `FileStream`'s class Javadoc: two paragraphs, "The files and the
  disk" and "A backup by a copy of the files" (section 4 below).
* `Database.maintain()`: "it brings the stream of a database that has
  been emptied to within about 400 kB of the stream of a fresh one".
* Tests: `testFileSizeRules0` and `testFileSizeRules1` (unit) and
  `tFileSizeIncrease` (f) for the tenth; `testMixedFileSizes` (unit,
  new, section 2); `DbTesterStream.testZeroedTailOverMetaBlock` (f,
  028-60) made its 1 MB last file at 4 MB, where the quarter began 1 MB
  files, and makes it at 10 MB now.
* `java/stress/ReclaimCost.java` prints the disk's parts (`DISK
  PARTS`), section 3.
* 027-13, section 4; 027-14; 033, RB-011; `releases/next.md`.

The stream's bytes are the same: only the files' boundaries move. In
both measurements below the stream's length, fp and every cut are the
same before and after.

### 2. A start with files of both rules

`testMixedFileSizes` makes by hand a directory as the quarter makes it,
twenty 200 kB files to 4 MB, six 1 MB files to 10 MB and a last 1 MB
file half full, which the tenth would not make (it begins 1 MB files at
10 MB), and opens it: every byte reads back. It then cuts at 9.5 MB
(the files before 9 MB go), appends 1.5 MB, which fills the old last
file and makes 200 kB files, as the tenth gives for 2 MB of stream,
opens the directory again, two 1 MB files of the quarter beside five
200 kB files of the tenth, appends, and opens it once more; the layout
and every byte are checked each time. A start checks only that each
file begins where the one before ends and that every file but the last
is a multiple of 100,000 bytes (`checkDbFiles`); it gives the last file
the smallest size not below the lengths of the last two files. So a
database written by 2026.6 opens, and its new files take the tenth.

### 3. The measurements

On F53 with `java/week.sh` running (load 9 to 12); `before` is `main`
at `8d86234b`, `after` the branch.

031-02's RetainChurn, through 028-61's probe `RetainChurnRows`
(`probes/run.sh` of 028-61), the emptied rounds, disk / stream kept:

* seed 5, round 0 (F2's case): before 10,400 kB / 61 kB (one file,
  from 280,000 kB, of 20 MB); after 400 kB / 61 kB (one file, from
  290,000 kB);
* seed 1, rounds 1 to 3: before 200, 2,600 and 3,800 kB; after 200,
  600 and 800 kB; the stream kept 36, 183 and 142 kB in both.

The bound after the change: an emptied database keeps, beyond the
stream, less than one file of about a tenth of the stream kept when the
file was made: up to 5 MB after 85 MB kept, where the quarter gave 20
MB.

A database written all the time: `ReclaimCost` with `disk=1` (K = 1,
uniform, 20 MB of live data, values of 1,000 bytes, the default f and
startup distance; no cache budget, as the harness has it; about 65,000
transactions a second, about 120 MB of stream a second; 7 cuts, the
stream kept 99.6 MB on average), sampled every 1,000 transactions after
the first cut, each divided by the stream kept:

* the part before fp of the file that fp lies in (what 027-13's 6 to 9
  percent was): before mean 0.063, max 0.235; after mean 0.021, max
  0.055 (the same in each run: the stream is the same);
* the files that end before fp and are not yet deleted: before 0.24,
  0.35 and 0.44 in three runs; after 0.50, 0.51, 0.52 and 0.55 in four;
  most of them taken off by `FileStream`'s cut and waiting for its
  thread (before 0.17 and 0.34, after 0.37, 0.37 and 0.42), the rest
  for Reclaim's cut, which waits for durability;
* files on disk, mean: before 16 to 23, after 56 to 60;
* the disk: before 1.28 to 1.48 (six runs), after 1.49 to 1.56 (five).

So the tenth cuts the part of the file at fp to a third, and the 6 to 9
percent of 011-04, W5d, measured on 2026-10-13 when a cut deleted its
files on the committing thread, no longer describes the disk of a fast
writer: since 005-46 the cut's thread deletes the files one at a time,
the directory forced after each (about 6 ms a file on F53 alone:
[probes/DelRate.java](probes/DelRate.java), 91 files of 60 MB in
0.52 s), and a writer of 120 MB a second is ahead of it; with
about three times as many files the lag is larger. A slower writer has
less of it, in proportion to its rate. Not changed here; for the lead
(section 6).

### 4. The backup property, from the code

* `FileStream` writes a file only by `DbFile.append`, at the file's
  end (it checks the length on disk first); it has no write at a
  position, no truncation and no rename (`renameAsDelete` is never
  set). Recovery after a crash appends too (`RecoverableStream`
  completes a torn record at the end). A start opens the files as they
  are.
* Files are removed only whole: a cut takes off the files that end
  before its position, never the last, and its thread deletes them
  oldest first, forcing the directory after each (`runCuts`);
  `seekFirstPos` deletes all, for the class's own tests only.
* So a copy of the `*.bergdb` files of a stopped database is the
  database. A copy of a running one that lists the files and copies
  them in the order of their names, the last one last, holds every file
  before the last whole, as they never change, and the last up to where
  the copy read it: the stream as a kill of the process would leave it
  then, and a start takes it as after a kill (its end may be torn; on
  macOS possibly zeros, as RB-012's). A file that a cut deletes while
  the copy reads it stays readable on macOS and Linux; the copy then
  holds files that the stream has deleted, as after a crash before a
  cut's deletes, and the start cuts again. A listed file that a cut
  deleted before the copy opened it is missing, and the copy must be
  taken again: with a gap, a start refuses it (`BadDirStateException`);
  missing only its first files, it can lack the record of their cut,
  which may be in a file made after the listing. `bergdb.lock` is not
  needed. Not run on Windows, where a delete of a file that a copy
  program holds open can fail, which fails the stream.
* Checked by [probes/BackupCopy.java](probes/BackupCopy.java): a Pub
  database written all the time (1.5 kB values, a retain duration of 1
  s, so reclaim cuts and files go during the copies), copied 100 times
  as above, each copy started and holding the state after one of the
  writer's transactions; 29 copies were taken again for a missing file;
  up to 118 files; BACKUP COPY OK.

### 5. Gates

On the branch's final code, F53 loaded: `java/before-commit.sh`: BEFORE
COMMIT OK (79 s; unit 1,755 tests, among them `StreamContractTester`'s
8 and `FileStream`'s, f 90); `java/stress/kill-restart.sh 200`: KILL
RESTART OK, 200 kills and 8 exits in 297 s, seed 20261126. The first
run of before-commit.sh failed in two f-tests that assumed the quarter's
files (`tFileSizeIncrease`, `testZeroedTailOverMetaBlock`), both moved
to the tenth (section 1).

### 6. For the lead

* The cut's thread and a fast writer (section 3): the disk of a
  database written at about 120 MB a second is 1.5 times its stream,
  most of it files waiting for deletion, a little more with the tenth.
  A change, such as forcing the directory less often, would have to
  keep each delete persisted before the next (`runCuts`); not looked
  into.
* The C clone (012, 022) keeps the quarter (`stream.c`), as it follows
  a release, not `main`.


Log
---

2026-11-25. Registered by lead-1125, from 028-61.

2026-11-26. Frans's decision: neither J nor S; a tenth, the Javadoc of
the stream, `FileStream`'s Javadoc of the disk and of a backup by a
copy of the files. Done by an agent of lead-1126 (clone c62, branch
`028-62`): RetainChurn's case at 400 kB on disk, from 10,400 kB; a
start accepts files of both rules (`testMixedFileSizes`); the backup
property checked in the code and by a probe. Status done.
