028-81. Fix: another database's first stream file is refused with a wrong cause; created.txt's ID not read
==========================================================================================================

Status: in progress (built and gated on the branch `028-81-82`, to
land).
Kind: Fix. Frans: none.
Created 2026-11-28 by Frans Lundberg.

What: 031-08, part B, UB-3 (`items/031-release-2026-7/08-user-apps/`,
`apps-b.md`, section 4; its probe `probes/ForeignFileProbe.java`, mode
`first`), product, low severity. With another database's first stream
file, of the same name and length, in place of the database's own, the
start is refused with a `BadTailException` whose cause is wrong: "The
header of the record at 206200 is not one of this database's records at
its place (bergdb 028-67, C3). The stream's records end at stream
position 206200 ..."; the database's own records after the first file
are what it calls not the stream's. Its way out, a cut of the stream
there and the later files removed, leaves a database of 6 keys, every
value the other database's. The start takes the database's ID from the
stream's first meta block (`RecoverableStream.readFirstMetaBlock`, 027-11,
1.2, step 3), and every later block and record is checked against it;
`created.txt` names the database's own ID ("database ID: ..."), and the
start did not read it. So also the stream files of one database beside
the `created.txt` of another were taken as that database (f4's case "B's
stream files with A's created.txt").

Checked on `main` at `4d2cb284` (2026-11-28, after 028-70 and 028-80):
`ForeignFileProbe first` gives the same refusal ("The header of the
record at 206200 ...") and, after the way out, "6 keys, by the first bytes
of their values: {B:=6}".

Why: a refusal names the cause and the way out (028-67, R1); here both
are wrong, and the way out gives another database's values. Nothing is
lost while the copy that the message asks for is kept, and the refusal
writes nothing.

Frans: none.

Done when: where the directory has a `created.txt` that names an ID, the
start compares it with the stream's first meta block's ID, and with the
ID that the rest of the checks use, before anything else, and refuses a
mismatch with a message in the form of 028-66's for a file of another
database (the files, both IDs, the way out: restore the database's own
files from a backup; nothing written or deleted); the start trusts
`created.txt` for nothing else; tests that fail before: the probe's mode
`first` as a unit test on files, a `created.txt` of another database
beside this one's stream files, and a database without `created.txt`
that starts as before; `java/before-commit.sh` prints `BEFORE COMMIT
OK`; 027-11 agrees with the code.

First step: `Db.startInner`, `writeCreatedTxt`, `DatabaseBuilderImp`'s
handling of `created.txt`.

Found by: 031-08, part B (UB-3), 2026-11-28.

Not in this entry: UB-4, another database's file in the middle, accepted
and read with no error, as the documents allow; it is in 028-77's scope
(node checksums with the database's ID and the position).


Result
------

On the branch `028-81-82` (2026-11-28).

* **Where `created.txt` is written and read.** `Db.writeCreatedTxt` writes
  it with the line "database ID:   " and the ID in 32 hex digits: at the
  end of the creating start, after both records of the creation are
  synced (028-18), and at a later start that finds it missing
  (`writeCreatedTxtIfMissing`, with the stream's ID and the creation
  date unknown). Only with `DbBuilder.createdTxt(File)`: the Pub API sets
  it for a directory's `FileStream` (`DatabaseBuilderImp.handleCreatedTxt`);
  a Core API user without it has none. Before this entry the Pub API
  read `created.txt` only for its existence (`refuseMissingStream`) and
  its line "crypto key:" (`refuseEncrypted`, 020-28); the Core never read
  it. Every database of this format (meta version 156) was made by a
  build of 2026.7, whose `created.txt` has the line.
* **Built.** `Db.refuseCreatedTxtOfAnotherDatabase`, called by
  `startInner` on a start that does not create the stream, before every
  other check of it (before the refusal of an incomplete creation, the
  node size and recovery): with `created.txt` that names an ID (32 hex
  digits, not all zero) and a first meta block that is valid and holds
  its own position (`RecoverableStream.readFirstValidMetaBlock`, the block
  that recovery takes the ID from; null where recovery refuses the
  stream, which it then does as before), another ID is refused with a
  `StreamIoException` whose cause is a `BadDirStateException`, as 028-66
  refuses a file before a gap of another database. After recovery's walk
  the ID that the start took, the meta block in memory's, which every
  block and record is checked against, is compared with `created.txt`'s
  again (the same block's ID by `readLastValidMetaBlock`; the comparison
  holds the start to it whatever changes later). The start takes nothing
  else from `created.txt`. Not compared: a start without `created.txt`
  (the Core API, a lost `created.txt`, which the start writes again from
  the stream), with one that names no ID that reads as one, and the
  creating start. Both cases of a mismatch are refused, another
  database's first file and a `created.txt` copied with the wrong files:
  the files do not belong together, and the start cannot tell which of
  them is the database's.
* **The message**, for ForeignFileProbe's case: "The stream's first meta
  block, at 0, in the stream file 00000000000000.bergdb, holds the
  database ID B, and created.txt in D names the database ID A: the stream
  files and created.txt are of two databases, and either may be another
  database's, as when another database's first stream file is put in
  place of the database's own, or the stream files of one database
  beside the created.txt of another (bergdb 028-81). The start, which
  checks this before it reads the rest of the stream, has written and
  deleted nothing. To start the database, restore its own files from a
  backup, the stream files (*.bergdb) and created.txt all together, and
  keep the files that are there now: they may be another database's."
  The file is named by `FileStream`'s names in the directory of
  `created.txt` (the file of the largest first position at or before the
  block), and left out if there is none.
* **Javadoc**: `Db.start()`, `DbBuilder.createdTxt`, `DatabaseBuilder.start()`,
  `Database`'s "The files"; 027-11, 1.2, step 1, sections 3, 6 and 7.

Tests (`DbTesterStream`, on `FileStream`s with `created.txt`, as the Pub
API starts them):

* `testFirstFileOfAnotherDatabaseRefused`: A and B made by the same puts
  with other IDs; B's first file in A's directory: refused, the message
  with the file, both IDs and the way out, every file byte for byte as
  before; with A's file back, A starts with its values. Before the fix:
  `BadTailException: The header of the record at 201424 is not one of
  this database's records at its place (bergdb 028-67, C3) ...`.
* `testCreatedTxtOfAnotherDatabaseRefused`: B's stream files with A's
  `created.txt`: refused, the files as before; with B's `created.txt`, B
  starts. Before the fix: started (`AssertionError: started`).
* `testStartWithoutCreatedTxtIdAsBefore`: without `created.txt` the start
  writes it with the stream's ID; a `created.txt` with no ID line, a short,
  a damaged and an all-zero ID: started, the file unchanged; a start
  without `createdTxt(File)` beside another database's `created.txt`:
  started. Passes before and after.


Gates
-----

On F53 beside other sessions' runs (load averages near 20), 2026-11-28,
on the branch `028-81-82` rebased on `main` at `ead07411` (031-08's part
B landed), at 028-82's commit, which holds 028-81's:

* `java/before-commit.sh`: BEFORE COMMIT OK (130 s; unit 1,767 tests, f
  96).
* `java/stress/level3.sh`: LEVEL 3 OK on the second run (its power-loss
  stage: POWERLOSS OK, 8 seeds, 488 cold recoveries). The first run
  failed at its unit tests, at
  `PubTesterJavadocNewUsers.testNewDatabaseWhereAStoppedOneWasDeleted`
  ("Could not find *any* valid meta block ... The stream begins at
  200000 ... The stream's first file in .../doc is
  00000000000002.bergdb"), the failure of 021-20's case: the old
  database's background close makes its next stream file in the
  directory made again at the path, in the window between
  `FileStream.checkDirectory()` and the step that 021-20 and 021-24
  leave open. Not reproduced: the test passed in both runs of
  `before-commit.sh`, in level3's second run, and 40 times of 40 alone
  on the branch.
* `java/stress/apps.sh quick`: APPS OK (every app compiled, 031-08's f1
  to f5 among them).
* f4 `FileHandling`, seeds 7, 8 (with a database of release 2026.6) and
  14, as 031-08's section 3 runs it, before (on `main` at `4d2cb284`) and
  after: OK in each; before 46, 41 and 52 accepted, after 45, 40 and 51,
  the one case of each seed that changed being "B's stream files with
  A's created.txt", now refused by 028-81 (f4 expects either); every
  refused start changed no file, and every directory whose cause was
  removed started with every transaction. f4 matches no message text
  that 028-82 changed.
* `PowerLossTest 1001 12 3000 3`: POWERLOSS OK, 12 seeds, 732 cold
  recoveries, without per-append forces 744; negative controls caught.
* After these, 028-82's commit took a Javadoc-only addition, part A's
  UA-1 of the same finding and that `sync()` makes no cut, on `main` at
  `32b7e6f1` (031-08's part A landed: apps and probes only):
  `java/before-commit.sh`, BEFORE COMMIT OK (86 s; unit 1,767 tests, f
  96).


Log
---

2026-11-28. Registered by lead-1127 from 031-08's UB-3; taken by an
agent of lead-1127, on the branch `028-81-82`.

2026-11-28. Built: `created.txt`'s ID against the first meta block's,
before every other check; the three tests, two failing before.

2026-11-28. The gates passed (above), on the branch rebased on `main` at
`ead07411`, and before-commit.sh again on `32b7e6f1`; to land.
