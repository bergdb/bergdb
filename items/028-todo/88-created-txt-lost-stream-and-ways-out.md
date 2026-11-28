028-88. Fix: with created.txt, a stream that lost its bytes is refused as a creation; two refusals name no way out; a cut created.txt is not written again
==========================================================================================================================================================

Status: done (2026-11-28): on `main` (`c2b1c826`, `d5bf7ba0`).
Kind: Fix. Frans: none.
Created 2026-11-28 by Frans Lundberg.

What: the three findings of the second review of the start and recovery
path of 2026-11-28 (033, `reviews/2026-11-28-start-2.md`, F1 to F3), all
S4 (033's rules), on `main` at `2b3755ab`.

* **F1.** With `created.txt`, a stream file of zeros, or cut to a part
  of the creation (1 to 415 bytes), is refused as a creation that did
  not complete (`DatabaseNotCreatedException`, "Remove its files and
  start it again"), with `create()` and with `open()`. `created.txt` is
  written after the creation's records are synced (015-01, 028-18), so
  the database was created and may have held data: a storage that lost
  the file's bytes and kept its length leaves such a stream. An
  application that removes the files, as the exception says, makes a new
  database where one was lost. A stream file of 0 bytes gives 015-01's
  `DatabaseMissingException` instead. The probes: `PubCreatedTxtProbe`
  (the Pub API), `CreationKillProbe` (the Core API, 272 and 416 images).
* **F2.** Two of the four refusals of a stream that lacks bytes name no
  way out: `RecoverableStream.checkLastTransSpos`'s and `recover()`'s
  "Could not find *any* valid meta block" (for a stream from 0 with no
  cause either). 028-82 gave the way out to the other two,
  `Db.refusalOfMissingBytes` and `Reclaim.initFromDb`'s. The probe:
  `RefusedStartProbe OUT 1`, every stream file but the last removed.
* **F3.** `created.txt` is written with `Util.bytesToFile`, a
  `FileOutputStream` that empties the file and writes it, with no force,
  and `Db.writeCreatedTxtIfMissing` writes only a missing one: a
  `created.txt` that a kill or a power loss left empty or cut is never
  written again, and 028-81's comparison is never made for that
  database. The probes: `PubCreatedTxtProbe` (with an empty `created.txt`
  the start took another database's stream file), `StartChain2
  -Dtxt=on` (a cut one left as it was in 255 of 255).

Checked on `main` at `3726bb18` (2026-11-28) with the review's probes:
`PubCreatedTxtProbe` gives the four `DatabaseNotCreatedException`s of
F1 and, for F3, "created.txt empty, the other database's stream file in
the stream file's place, open(): started, /k/note.txt reads of b;
created.txt after it: 0 bytes"; `RefusedStartProbe OUT 1` gives F2's
message, which ends with the storage's account and no way out.

Why: a refusal names the cause and the way out (028-67, R1); F1's way
out loses a database, F2's refusals have none, and F3 leaves 028-81's
check off for good.

Frans: none.

Done when: with `created.txt` such a stream is refused as one that lost
bytes, the files kept, the message naming `created.txt`, the stream file
and the way out, a restore from a backup, never the removal of the files;
the two refusals end with 028-82's way out; `created.txt` written whole
and durably, and a start that finds one without a valid "database ID:"
line writes it again from the stream after its last check; 027-11 and
the Javadoc of `DbBuilder.createdTxt` say what `created.txt` holds and
when it is written; tests that fail before; the gates below.

First step: `Db.refuseIncompleteCreation`, `writeCreatedTxt`,
`writeCreatedTxtIfMissing`, `RecoverableStream.recover` and
`checkLastTransSpos`.

Found by: the second review of the start and recovery path of 2026-11-28
(033, `reviews/2026-11-28-start-2.md`, F1 to F3).


Result
------

On the branch `028-88` (2026-11-28).

* **When `created.txt` is written** (read for the rule): at the end of
  the creating start, after `syncCreation` has made both records of the
  creation durable (028-18), and at a later start that read the stream,
  after its last check (`writeCreatedTxtIfMissing`, after
  `Reclaim.initFromDb` and the held writes; 028-66, 028-70). A later
  start reads only bytes that `FileStream`'s open has forced (the last
  file at the open, `Force.OPEN`). A Core start with `createdTxt(File)`
  on an empty stream in a directory that has `created.txt` created the
  database and wrote `created.txt` again at its end, so a kill inside it
  left the older file beside a part of the creation; the Pub API refuses
  such a directory before (015-01). Built: the creation removes a
  `created.txt` that is there, and forces the directory, right before
  its first byte is appended (`Db.writePrimordialTransaction`; a failure
  fails the start with nothing appended). So `created.txt` is there only
  once a creation's records are durable in the stream.
* **F1, built.** `Db.refuseIncompleteCreation`: on a start that did not
  create the stream, with `created.txt` there (a file), a stream that
  `isIncompleteCreation` or `holdsPrimordialRecordAlone` takes is refused
  with a `DatabaseMissingException` (015-01's exception of a directory
  with `created.txt` and no stream byte, so an application handles a
  stream file of 0 bytes and one of zeros alike), after 028-81's
  comparison and before anything else. The message, for the review's
  probe: "The stream, of length 528, holds no data, only zeros or a part
  of a creation's records, and created.txt is in D: the database was
  created, as a creation writes created.txt only once its records are
  durable in the stream (bergdb 015-01, 028-18), and its stream file
  00000000000000.bergdb lost bytes, as a storage that lost a file's
  bytes and kept its length leaves it, or another file was put in the
  place of the stream file. The start has written and deleted nothing.
  To start the database, restore its files from a backup, the stream
  files (*.bergdb) and created.txt all together, and keep the files that
  are there now; removed, a start would create a new, empty database in
  the place of the one that was lost (bergdb 028-88)." Without
  `created.txt` (the Core API, a lost `created.txt`) the refusal is the
  creation's, as before. Javadoc: `Db.start()`,
  `refuseIncompleteCreation`, `DatabaseMissingException`,
  `DatabaseNotCreatedException`, `DatabaseBuilder.start()`.
* **F2, built.** The way out of 028-82 is the storage's constant
  `RecoverableStream.MISSING_BYTES_WAY_OUT`, " To start the database, put
  its missing stream files back from a backup, or restore its files all
  together, the stream files and created.txt; a copy of a running
  database's files that missed some is taken again (bergdb 028-82).";
  `Db.MISSING_BYTES_WAY_OUT` is " The start has written nothing either
  (bergdb 028-70)." and it, so Db's and Reclaim's messages are as
  before. `checkLastTransSpos`'s message and "Could not find *any* valid
  meta block" of a cut stream end with it. For a stream from 0 the
  message is now "Could not find *any* valid meta block. At least the
  very first meta block must be valid in a db stream. No meta block is
  valid, also not the first, at 0, which the database's creation wrote:
  the stream is damaged from its start, as a storage that lost or
  changed the bytes of its first stream file leaves it, or it is not a
  BergDB stream. The start has written nothing. To start the database,
  restore its files from a backup, the stream files and created.txt all
  together (bergdb 028-88)." Every message keeps its beginning, which
  the review's chains and f4 match.
* **F3, built.** `Db.writeCreatedTxt` writes with `Util.writeFileDurably`:
  to `created.txt.tmp`, forced, renamed over `created.txt` (an atomic
  move) and the directory forced, as `FileStream` forces a file and then
  its directory; not interruptible, as `FileStream`'s forces (005-46).
  `writeCreatedTxtIfMissing` takes the ID that the start read from
  `created.txt` (028-81): where there is none, the file missing or
  naming no ID (no "database ID:" line, a short, damaged or all-zero ID),
  it writes the file again with the stream's ID and "creation date:
  unknown (created.txt written at a start on DATE)", at the same point
  as a missing one, after every check (a start that refuses writes
  nothing, 028-70). A `created.txt` that is not a file is left. Javadoc:
  `DbBuilder.createdTxt` (what the file holds and when it is written),
  `writeCreatedTxt`, `writeCreatedTxtIfMissing`,
  `DatabaseBuilder.create`.
* **027-11**: 1.2, steps 1, 2, 3 and 5; 1.9; sections 6 and 7; its log.

Tests, each failing before the fix and passing after it (2026-11-28; the
before run on `3726bb18` with the new tests):

* `DbTesterStream.testStreamLostBesideCreatedTxt` (F1): a file database
  of one stream file with a value synced, the file made zeros and cut to
  1, 100, 128, 200, 272 and 350 bytes: with `created.txt`, a
  `DatabaseMissingException` with the message's parts, no file changed;
  without `createdTxt(File)`, a `DatabaseNotCreatedException`. Before:
  "DatabaseNotCreatedException: The database was not completely created
  ... of length 512 ...".
* `DbTesterStream.testCreationRemovesCreatedTxtFirst` (F1): a creation
  in a directory with a `created.txt`: none at the stream's first write,
  the new ID after the start. Before: "created.txt at the first write,
  expected false, but was true".
* `PubTester.testOnlyStreamFileZerosOrCut` (F1, the Pub API): zeros and
  a cut to 100 bytes, `create()` and `open()`: a
  `DatabaseMissingException`, nothing changed. Before: the
  `DatabaseNotCreatedException`.
* `PubTester.testFailedStartsDirectoryRemoved` (005-32), changed: its
  stream, cut to 200 bytes beside `created.txt`, is refused with a
  `DatabaseMissingException` now, and the directory is removed and
  created again as before. On the change's first form `before-commit.sh`
  failed there.
* `DbTesterStream.testStreamLacksBytesWayOut` (F2): four files of
  200,000 bytes, the first three removed, `checkLastTransSpos`'s message
  ends with the way out; 300,000 zeros from 0, "Could not find *any*"
  with the cause, "has written nothing" and the way out. Before: the
  first without the way out.
* `DbTesterStream.testStartWithoutCreatedTxtIdAsBefore` (F3), changed:
  a `created.txt` that names no ID (no line, short, damaged, all zero,
  empty, cut before, inside and at the 31st digit of the ID) is written
  again with the stream's ID; with B's stream files beside the rewritten
  `created.txt`, the start is refused by 028-81. Before: "the file
  unchanged" was the test's assertion, and the new one failed at the
  first text.
* `Util.testWriteFileDurably` (F3): the file replaced whole, no
  `created.txt.tmp` left, on an interrupted thread too, whose flag is
  kept; a durable delete.

The review's probes on the branch (2026-11-28): `PubCreatedTxtProbe`:
F1's four starts refused with the `DatabaseMissingException` above;
"created.txt empty, the database's own stream, open(): started ...;
created.txt after it: 196 bytes"; "created.txt empty, the other
database's stream file ...: StreamIoException: The stream's first meta
block, at 0, ... (028-81's refusal)". `RefusedStartProbe OUT 1`:
"REFUSEDSTART DONE: no start changed a file before it refused, and the
controls started", the case of every file but the last ending with the
way out. `CreationKillProbe`: the 688 images with `created.txt` there
(272 of zeros, 416 prefixes) refused with the `DatabaseMissingException`,
which the probe, written for the old rule, counts as BAD; every other
image as before.


Gates
-----

On F53 beside other sessions' runs, 2026-11-28, on the branch on `main`
at `3726bb18`:

* `java/before-commit.sh`: BEFORE COMMIT OK (85 s; unit 1,783 tests, f
  98). The first run failed at `PubTester.testFailedStartsDirectoryRemoved`
  (above).
* `java/stress/level3.sh`: LEVEL 3 OK (its power-loss stage: POWERLOSS
  OK, 8 seeds, 488 cold recoveries).
* `java/stress/apps.sh quick`: APPS OK. f4 `FileHandling` seed 1: 88
  cases, 51 accepted, 37 refused; its cases "created.txt of garbage
  bytes" and "created.txt empty" accepted, the start writing
  `created.txt` again (300 and 0 to 196 bytes; F3), which f4 allows.
* `StartChain2` (033, `reviews/2026-11-28-start-2-probes/`),
  `-Dtxt=on -Dstartkill=on -Dshapes=on ... 88000 88099 20 2 30 1 25`:
  "STARTCHAIN DONE seeds 88000..88099: starts 2000, faults {kill=1405,
  kill-in-recovery=113, kill-in-start=170, power=668, stale=201,
  stale-refused-with-P=119, stale-started=71, stale-zeros-first=61,
  txt-cut-started=88, txt-cut-written-again=88, txt-other-refused=80,
  txt-removed-written-again=74}, known (a) 49, failures 0": a cut
  `created.txt` written again in 88 of 88 (the review: left as it was in
  255 of 255).
* `RefusedStartProbe OUT 1`: "REFUSEDSTART DONE: no start changed a file
  before it refused, and the controls started".
* `PowerLossTest 1001 12 3000 3`: "POWERLOSS OK: 12 seeds, 732 cold
  recoveries; without per-append forces 744, and of 144 hole images 2
  recovered, 142 failed (a known limit, bergdb 014-01); negative
  controls caught".


Log
---

2026-11-28. Registered by lead-1127 from the review's F1 to F3; taken
by an agent of lead-1127, on the branch `028-88`.

2026-11-28. Built: F1, F2, F3; the tests, each failing before.

2026-11-28. The gates passed (above), on the branch on `main` at
`3726bb18`; rebased onto `main` at `f5f22893` (items only), where
`java/before-commit.sh` ran again; to land.

2026-11-28. Landed on `main` (`c2b1c826`, `d5bf7ba0`). Done.
