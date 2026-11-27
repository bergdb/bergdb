028-66. Investigate: the cut's deletes lag behind a fast writer
================================================================

Status: open. Kind: Investigate. Frans: decided (2026-11-27, 17:26: C with
the rule of the files before a gap, after a quiet timing run against `main`
and a review; section 4). C with the rule built on a branch (section 6).
Created 2026-11-26 by Frans Lundberg.

What: since 005-46 the cut's own thread deletes the stream files below a
cut one at a time, forcing the directory after each. 028-62 made a new
file a tenth of the stream kept, not a quarter, so a database has about
three times as many files. In 028-62's measurement (`ReclaimCost`, disk
on, 20 MB live, about 120 MB/s of stream), with 56 to 60 files against
16 to 23, a fast writer stays further ahead of the deletes: the stream
not yet deleted below the cut was 50 to 55 % of the stream kept, against
24 to 44 % with the quarter, and the disk over the stream went from 1.28
to 1.48 to 1.49 to 1.56. The part of the file that the cut lands in fell
from 6.3 % (at most 23.5) to 2.1 % (at most 5.5) of the stream kept.
027-13's 6 to 9 % dates from 2026-10-13, when the deletes were
synchronous.

Why: the disk a database takes beyond its stream; a tenth was chosen to
make it smaller (028-62), and the deletes' lag takes back part of that
for a writer that writes fast.

Done when: the lag measured at a few writing rates, with the quarter and
the tenth; a change such as deleting all the files below a cut with one
force of the directory, measured; or the reason it stays, written here.

First step: 028-62's result and `ReclaimCost`'s `DISK PARTS` line;
005-46 and `FileStream`'s deletion of files at a cut.


Result
------

Done 2026-11-26 by an agent of lead-1126, on the branch `028-66` of a
clone of `main` at `f461b66a`.

### 1. The measurement

`ReclaimCost` with `disk=1`, `live=20000000` (as in 028-62: K = 1,
uniform, values of 1,000 bytes, the default f and startup distance, 7
cuts, the stream kept 99.6 MB on average), and a new property `rate=X`:
phase 3 appends at most X MB of stream a second, the writer sleeping
when it is ahead. Time is simulated, so the stream, fp and every cut are
the same at every rate and in every variant; only the deletes' timing
differs. Three variants, run interleaved, 3 to 7 runs each:

* quarter: `main` at `8d86234b`, before 028-62;
* main: `main` at `f461b66a`, the tenth, a directory force after each
  deleted file;
* batch: main with the change of section 2
  ([batch-delete.patch](batch-delete.patch)).

On F53 beside `java/week.sh`'s large run (load 3.7 to 5.8), 15:49 to
15:58; the figures are indicative. Each cell: the disk / the stream
kept, mean; the files that end before fp and are not deleted / the
stream kept, mean; the files on disk, mean.

| MB/s | quarter | main | batch |
|---|---|---|---|
| 10       |                             | 1.05, 0.03, 24              | 1.03, 0.02, 22              |
| 30       | 1.10, 0.05, 9               | 1.09, 0.08, 28              | 1.03, 0.03, 23              |
| 60       | 1.13, 0.08, 11              | 1.15, 0.14, 35              | 1.05, 0.04, 24              |
| 100      | 1.17, 0.12, 13              | 1.32-1.41, 0.32-0.41, 47-52 | 1.05, 0.04, 24              |
| no limit | 1.39-1.44, 0.35-0.40, 21-22 | 1.43-1.58, 0.45-0.59, 54-63 | 1.10-1.15, 0.11-0.17, 26-30 |

* With a force after each file, the lag grows with the rate: of it,
  the files that `FileStream`'s cut took off and its thread had not yet
  deleted were 0.05 of the stream kept at 30 MB/s, 0.10 to 0.11 at 60, 0.28 to
  0.35 at 100 and 0.33 to 0.45 with no limit (main); 0.02 to 0.03 at
  30 MB/s, 0.05 to 0.06 at 60 and 0.09 at 100 with the quarter. With the
  batch, at most 0.02 at every rate: the rest of its lag is the files
  that wait for Reclaim's cut, which waits for durability.
* The writer: with no limit, main made 63,000 to 68,000 transactions a
  second (about 120 MB/s of stream), the quarter and the batch 102,000
  to 109,000 (about 195 MB/s). A directory force is an `F_FULLFSYNC`
  on macOS, a flush of the device's cache (011-07), and the cut's
  thread's forces, one per file, take turns with the writer's forces.
  So with the tenth and a force per file, a writer with hard sync on
  F53 writes about 40 % slower than with the quarter; with the batch, as
  fast as with the quarter.
* The part of the file that fp lies in is 0.021 (at most 0.055) of the
  stream kept in main and the batch alike, as in 028-62.

### 2. The change measured

`FileStream.runCuts` deletes a batch, the files that the cuts so far
took off, oldest first, and then forces the directory once; files that
a cut takes off meanwhile are the next batch. Deletes stay on the cut's
thread, off the commit path (005-46); the force of the stream up to the
latest cut's length before a batch stays (005-47); a failed delete or
force is the stream's failure as before; files are still deleted whole,
oldest first, so the backup property of `FileStream`'s Javadoc (028-62)
holds as it is written. A new unit test,
`testCutDeletesABatchWithOneDirectoryForce`, checks the order and the
forces of two batches and a restart. The patch is in this entry; it is
not on `main`.

On the patch (2026-11-26, F53 loaded): `FileStream`'s unit tests and the
new one pass; two of `FileStreamPowerLossTester`'s fail (section 3);
`java/stress/kill-restart.sh 200`: KILL RESTART OK, 200 kills and 8
exits in 275 s, seed 20261126 (a kill of the process leaves the
kernel's directory as it is, so it does not test the order of section
3). The branch's commit, without the patch: `java/before-commit.sh`
BEFORE COMMIT OK (75 s).

### 3. Why it is not landed: the order within a batch

The order within a batch matters, and the change gives it to the file
system. 011-07 (the durability of level 3) states the rule that the
force after each file keeps: forcing only after the whole batch permits
an older name to survive a power loss while a newer one disappears,
which leaves a hole that `FileStream` refuses at its start
(`BadDirStateException`) before it can read the reclaim table. POSIX
does not order directory changes without a force between them. The
power-loss model (`FileStreamPowerLossTester`) takes that view: an
unforced unlink may survive while an earlier one rolls back. With the
batch, two of its unit tests fail as they should:
`testRecoveryBetweenEveryPrefixDeletion` (it asserts at most one delete
between directory forces) and
`testPartialDeletionAndDirectoryFailureKeepForcedBytes` (no delete after
a failed directory force; the batch deletes all its files before its
one force). `java/stress/flush-order.sh`'s check requires a
directory force between prefix deletions. 005-46 kept the deletes' order
for this argument ("the deletes and forces reach the disk in today's
order, so the power-loss argument holds as it is").

A file system that commits metadata changes as transactions in the
order made (APFS; ext4 and XFS with their journals) leaves a prefix of a
batch deleted at a power loss, and the batch is then as safe as today;
the hole needs one that does not. The files before such a hole all end
before a cut whose decision was durable, so deleting them by hand
starts the database. The change was therefore measured and kept out of
`main`; the code is as it was.

### 4. For Frans

Frans's decision, 2026-11-27, 17:26, on option C as designed (on the
branch `028-66c`, `e6900401`, section 5, not on `main`), as the lead
recommended:

1. A start deletes the files before a gap only if their first meta
   block is this database's (028-67's check of the database's ID, C1),
   and else refuses. C does not land before this rule is in.
2. C replaces A for 2026.7, after a timing run on a quiet machine
   against `main`, this rule and a review. So C lands after 031-06's
   landing step 4, the format, which brings 028-67's ties.

A stays on `main` until then.

* **A. As it is.** A force per file. A writer of 100 MB/s or more keeps
  1.3 to 1.6 times its stream on disk, and with no limit writes about
  40 % slower than with the quarter (section 1).
* **B. The batch** ([batch-delete.patch](batch-delete.patch)). One
  force per batch; the disk at 1.03 to 1.05 of the stream up to 100
  MB/s. Rests on the file system keeping the order of the unlinks of a
  batch; the rule of 011-07 and the power-loss model change: the model's
  unordered unlink becomes a known case in which a start refuses the
  directory until the files before the hole are deleted, its two tests
  and `flush-order.sh`'s check are changed to a batch, and `FileStream`'s
  Javadoc says so. Gates then: `java/before-commit.sh`,
  `java/stress/level3.sh` (the power-loss tests),
  `java/stress/kill-restart.sh 200`.
* **C. A batch that the model accepts.** A start that removes the
  files before a hole when they all end before a durable record of the
  storage's first position (for example a small file of `FileStream`'s,
  forced once before each batch), so that no power loss can leave a
  directory that a start refuses. One flush for the record and one for
  the directory per batch. Not designed; it adds a file to the
  directory, which the backup property of 028-62 must then cover.


### 5. Option C designed

Done 2026-11-27 by an agent of lead-1127, on the branch `028-66c` of a
clone of `main` at `dd62fc27` (c66c), not pushed; from the principle
that Frans decided on 2026-11-27: the stream is the bytes from
reclaim's cut to the end, and what the storage still holds before the
cut belongs to the storage's implementation. Frans had C designed this
way the same day; A stays on `main` until C lands. Each statement below
is marked: ran (a test or a run on the branch), read (the code or a
maintained document) or inferred.

#### 5.1. The rule, as built

* **The deletes.** `FileStream`'s cut thread deletes a batch: the files
  that the cuts so far took off, the deletes issued oldest first, then
  one force of the directory (`runCuts`, section 2's change). Before a
  batch it has the stream forced up to its length at the latest cut
  (`forceTo`, 005-47), a no-op with per-append forcing on.
* **The open.** A gap, a file that begins after the end of the one
  before it, is not refused (`checkDbFiles`): the stream is the files
  after the last gap, its first position the first of them's; the files
  before it, the leftovers, are not opened or read. A read below the
  first position throws `ReadBelowFirstPosException`, whose message
  names the directory, the bytes that no file holds and the leftovers.
  Still refused (`BadDirStateException`): a bad name, a file that begins
  before the end of the one before it, and a file but the last whose
  length is not a multiple of 100,000, leftovers too. For the tail of
  zeros (028-60) the stream's only file is counted among the files after
  the gap, so the next open, after the leftovers are gone, finds the
  same stream.
* **The leftovers' delete.** The first `pretruncate(pos)` with `pos` at
  or after the first position queues the leftovers, oldest first,
  before the files that it takes off, in the same batch; a cut before
  the first position deletes none of them.
* **The start** (`Reclaim.initFromDb`). After it reads the table, with
  fp the cut (0 if none): if the storage's first position is after fp,
  the start refuses with a `StreamIoException` whose cause is a
  `ReadBelowFirstPosException`, the storage's exception of a missing
  stream file (`DatabaseBuilder.start()`), "The stream begins at F,
  after reclaim's cut, C: the stream lacks bytes of the database from C
  to F. The start has deleted nothing", and nothing is cut; if
  it is before fp, the start cuts at fp, as it does after a crash
  between the table and the cut, and that cut deletes the leftovers.
  `Db.start` turns a failure of a start whose cause is a read below the
  first position into the same kind of refusal ("The start needs bytes
  of the stream before its first position"), and `RecoverableStream`'s
  two refusals before recovery writes (no valid meta block; the last
  valid block names a record before the first position) say the same
  when the stream begins after 0. Each message ends with the storage's
  account: the message of a read of the byte before the first position,
  which for `FileStream` names the gap.

#### 5.2. What a start reads before it knows its cut

The idea holds as stated: a start reads its cut using only bytes at or
after the cut, so a gap before the cut does not hinder it, and the
variant with the cut in the meta block is not needed.

* Recovery reads the meta blocks from the end down to the first
  position and stops at the last valid one, which names a record at or
  after every decided cut: a cut is decided only when the record that
  the last valid block names is at or after pCut
  (`pretruncateIfPossible`), and later blocks name later records (read).
* The startup pos of the last record is at or after the cut: the cut
  waits until the startup pos has reached pSafe, after pCut, and the
  startup pos never moves back (read: Reclaim's class comment).
* The section from the startup pos, the top node, the got-dirty nodes
  (`DbStarter`), the KVs of the startup distance and of reclaim's
  settings, the table and the current row: every node and value
  reachable in the latest state is stored at or after the cut (read:
  Reclaim's class comment; 027-11, section 1.10, "recovery and the
  section are after the cut").
* The restarts on `CutStream`, whose reads below the cut throw, check
  it: `Reclaim.Tester`'s cut tests and `ReclaimStress` in level 3 (ran,
  section 5.7).

So with the cut C at or after the gap's end H, the start reads only
files after the gap and reaches C. With C before H, either a read of
the start is below H, which can only be then, or the start reads C and
compares it with H; both refuse. A refusal deletes nothing (ran). It
writes nothing when the stream ended cleanly (ran: the files compared
byte for byte); after a crash, recovery may first complete a torn end,
only when the last valid meta block is after the gap, and then with the
bytes that a start with the missing files would write (inferred:
recovery reads only from that block on); the same holds for today's
refusals after recovery (028-70).

#### 5.3. The cases

1. **A batch under the power-loss model.** Any subset of a batch's
   unforced deletes survives. Every missing file was deleted by a cut
   whose table was durable first (5.4), so H is at or before the cut of
   the durable table: the start takes the stream and its cut deletes
   the leftovers. Ran: every subset of a batch of four files
   (`testRecoveryAfterEverySubsetOfABatch`, 11 of 16 with a gap); the
   traces' images with gaps, each started and checked (5.6).
2. **Two holes or more.** They come from one batch: a power loss loses
   only the deletes of the batch whose force has not returned. The
   stream is the files after the last gap; the files between the gaps
   are older than a deleted file, so a cut took them off (cuts take
   prefixes), and they are leftovers too. Ran: `testGapsAtOpen` (two
   gaps), the subsets with two gaps.
3. **A file of the live stream removed by hand.** C is before H: the
   start refuses, names the gap, and leaves the files as they were. Ran:
   `testStartRefusesAStreamThatLacksBytes`. A leftover removed by hand
   (a file that ends before C) is case 1 (inferred).
4. **The first files removed by hand, no gap.** The first position is
   after C (0 for a database never cut): refused. Before, a start that
   read before the first position was refused with that read's
   exception (`PubTesterJavadocNewUsers.testStartWithTheFirstFileDeleted`),
   and one that did not went on, and reads of the missing bytes failed
   the database later (inferred); now both are refused. Ran: the same
   test, its second part.
5. **A backup copy in name order taken while a cut runs** (028-62's
   backup property). Deletes are still issued oldest first, and a copy
   sees the directory as the deletes leave it; a listed file that a cut
   deleted before the copy opened it is missing, so the copy has a gap
   (files copied before it) or misses its first files. The copy starts
   if it holds the table of the cut that deleted the missing files (C
   at or after H), and its start deletes the files before the gap; it
   is refused if that table is in a file made after the listing, and
   must be taken again, as before. Ran:
   [probes/BackupGap.java](probes/BackupGap.java), 028-62's `BackupCopy`
   that skips a missing file instead of taking the copy again: 100
   copies of a Pub database written all the time, with cuts (retain
   duration 1 s); 75 whole; 15 with a gap, 7 started and 8 refused; 10
   without their first files, 9 started and 1 refused; every copy that
   started held the state after one of the writer's transactions and had
   no gap after its start; every refusal said that the stream lacks
   bytes; BACKUP GAP OK. 028-60's barrier (a copy begins after an
   append since the open, or after `close()`) is unchanged: the
   leftovers' delete does not touch the last file's zeros, and a cut
   that takes stream files still cuts them first (read).
6. **A failed delete or directory force.** The thread stops at the
   failure, which is the stream's, as before; the file that failed and
   those after it stay queued, and no later cut deletes. The deletes of
   the batch before the failure are not forced, so a power loss then is
   case 1. Ran: `testPartialDeletionAndDirectoryFailureKeepForcedBytes`
   (a failed delete; a failed directory force after a batch of four).
7. **A hole at the very end, the last file missing.** Not a gap: the
   stream ends earlier, as before. A cut never deletes the last file,
   and its name was forced before it took appends, so only a removal by
   hand or a device that lost forced names leaves it; not this design's
   case (inferred).
8. **Files before a gap that are no leftovers** ("newer than the hole
   suggests": another database's, or an older copy of the same, put
   into the directory by hand). They are not read. If the stream after
   the gap holds its cut at or after H, it is a whole database by
   itself, and its start deletes them; before, the open refused the
   directory. No byte of the stream that starts is deleted, and that
   database has all its data; but files that a user put there by
   mistake can be deleted (question 1 of 5.10). Ran:
   `testStartDeletesAFileBeforeAGap` (a file of zeros at 0). Since
   Frans's rule (2026-11-27, section 6.2), refused unless the file's
   first meta block is the database's.
9. **A stream after the gap that is no database** (an empty or stray
   file): no valid meta block, or one that names a record before the
   first position, or a read below it: refused, nothing deleted (ran:
   the negative controls of 5.5 end in these refusals).

#### 5.4. The durability argument, step by step

1. Reclaim decides the cut C in a record that stores the table with
   the row marked cut (`pretruncateIfPossible`), and calls the storage's
   cut only when the stream is durable past that record (`cutIfDurable`,
   `pendingCutDurableAt`; with forcing off, written). (Read.)
2. `FileStream.pretruncate(C)` takes the files that end before C off
   the list and records the length then (`cutForceTo`), which is past
   the record. (Read.)
3. Before a batch, the thread forces the stream up to `cutForceTo`, so
   the record of every cut whose files are in the batch is on the device
   before the first delete is issued: with forcing on it is already
   (the append's force), with forcing off the force of the last file
   (`Force.CUT`) does it; every file but the last was forced before the
   switch to the next. (Read; ran: the negative control without that
   force is caught, 5.6.)
4. The deletes are issued, then the directory is forced. A power loss
   before that force returns can keep any subset of them: the model's
   assumption, no order on the device. After it, all are durable.
5. After a power loss, a missing file was deleted under a cut whose
   record survived (3), so it ends before that cut, which is at or
   before C', the cut of the durable table. The gap's end H is the end
   of a missing file, so H ≤ C'.
6. The start reads C' using bytes at or after C' only (5.2), finds the
   first position H at or before it, and cuts at C' (H, a file's start,
   is a meta block's position, where no record begins, so H < C'),
   which deletes the leftovers and the files of the stream that end
   before C', in one batch: back to step 4.
7. A power loss between the decision and the cut (before step 2) keeps
   every file, and the start cuts again, as today. A power loss between
   2 and 3 deletes nothing. With no missing file, no gap: as today.

#### 5.5. What changed in 011-07's rule, the model and the contract

* **011-07's rule** (an archive since 2026-10-26; the rule is now in
  `FileStream`'s Javadoc, "A gap in the files", 027-13, section 1.7,
  and 027-14). Before: each delete of a prefix is followed by a
  directory force before the next, so that a power loss cannot keep an
  older file and lose a newer one, which leaves a hole that the open
  refuses. Now, in plain sentences:
  * What: a file of the stream is deleted only after the record of the
    cut that took it off is on the device; the deletes of a batch are
    issued oldest first, and the directory is forced once after them; a
    start finds the stream's front at or before its cut.
  * When: at each cut (`pretruncate`), on the cut's thread, before each
    batch (the force up to the cut's length) and after it (the
    directory); at a start, after the table is read.
  * By whom: Reclaim (the record durable before the cut), `FileStream`
    (the force, the order, the batch, the open's gap), the start
    (`Reclaim.initFromDb`, `Db.start`: refuse, or cut and delete).
  * How it is checked: `FileStreamPowerLossTester` (the images of any
    subset of unforced deletes start; 5.6), `flush-order.sh` (5.6), the
    unit tests of 5.6.
* **The model** (`FileStreamPowerLossTester.ModelIo`): its deletes had
  three images, the delete durable at once, the latest rolled back, and
  only the latest kept (`unordered_delete`), which was the negative
  control of the order. It now adds `subset_delete`, a random subset of
  the deletes since the last directory force kept, and keeps the images
  with a gap in a bucket of their own (`gap_delete`); the trace holds
  the cut's thread and releases it every 300 commits, so that a cut
  thread deletes batches of up to three files, as for a fast writer.
  Every image, gaps included, must start, hold every acknowledged
  commit and the frontier, take a write, a sync and a restart, and its
  start must leave no gap (`verify`). The two tests that failed with B
  are tests of the new rule: `testRecoveryBetweenEveryPrefixDeletion`
  became `testRecoveryAfterEverySubsetOfABatch`, and the second half of
  `testPartialDeletionAndDirectoryFailureKeepForcedBytes` checks a batch
  of four deletes before its failed force and no delete after it. The
  negative control `testUnorderedUnforcedDeletionsAreDetected` became
  `testUnorderedUnforcedDeletionsLeaveAGapThatOpens`. The negative
  controls of the weakened file force, of the directory force and,
  without per-append forces, of the forces before a new file and before
  a cut's deletes are still caught; a start refused for a gap counts as
  caught.
* **`flush-order.sh`**'s validator: no directory force between two
  deletes is required; the deletes must be in the order of the files'
  names, each after the files that survive it are forced, with a
  directory force after the last, and the probe must make a batch of
  two.
* **The stream contract.** `AppendOnlyStream`'s "CRASHES" gets a
  sentence: the front may move forward at a crash, never past the
  position of a `pretruncate()` made before it, and a caller that cuts
  makes its record of the cut durable before it calls `pretruncate()`.
  `StreamContract` and its tester check no reopen and are unchanged;
  `MemoryStream`, `OneFileStream` and `CutStream` are unchanged (read):
  they have no files to lose a delete of.

#### 5.6. The tests

* `FileStream` (unit): `testRestartMissingFile` (until now, the open
  refused; now it opens from the file after the gap, a read below names
  the gap, a cut before the first position deletes nothing, one at it
  deletes the leftover); `testRestartRefusedOverlap` (an overlap and a
  bad size before a gap still refused, the lock released);
  `testGapsAtOpen` (two gaps; one batch, the three leftovers and a file
  of the cut, one force; a lone file of zeros after a gap is in the
  stream); `testCutDeletesABatchWithOneDirectoryForce` (section 2's);
  `testReplacedRightBeforeTheOpen`'s comment.
* `FileStreamPowerLossTester` (unit and f): the tests of 5.5;
  `testStartRefusesAStreamThatLacksBytes`,
  `testStartDeletesAFileBeforeAGap`; the traces, which print
  `largest_batch` and `gap_images`: in level 3's 16 traces (8 seeds,
  with and without per-append forces) batches of up to 3 files and 3 to
  6 images with a gap each, 70 to 76 in all in its two runs, every one
  started and checked.
* [probes/BackupGap.java](probes/BackupGap.java) (case 5), by hand.

#### 5.7. The gates

On F53, 2026-11-27, beside other sessions' runs (level 2 and 3 of
031-06's landing, its user apps; load 9 to 34):

* `java/before-commit.sh`: BEFORE COMMIT OK (93 s; unit 1,731 tests,
  f 90) on the branch's first commit; BEFORE COMMIT OK (64 s) on the
  final tree. Its first run failed in one unit test,
  `PubTesterJavadocNewUsers.testStartWithTheFirstFileDeleted`, which
  asks for a
  `StreamIoException` whose cause is a `ReadBelowFirstPosException`
  when the first stream file is missing, as `DatabaseBuilder.start()`
  says; the refusals of 5.1 were `StreamFormatException`s then, and
  became that exception.
* `java/stress/level3.sh`: LEVEL 3 OK (17:03 to 17:12): every step, the
  power-loss stage POWERLOSS OK, 8 seeds, 488 cold recoveries, without
  per-append forces 496, among them 70 images with a gap, negative
  controls caught; conformance reclaim 40 traces and crash 15,
  TRACECHECK OK; InterruptStress 60 s. Its first run passed steps 1 to
  7 (the unit and f-tests, ReclaimStress, RestartInvariance, CrashTest,
  ReclaimReaders, LoadTest, and PowerLossTest: POWERLOSS OK, 8 seeds,
  488 cold recoveries, without per-append forces 496, negative controls
  caught) and failed in step 8 with `ClassNotFoundException:
  bergdb.core.TraceExport`, as this agent's `before-commit.sh`, started
  and stopped during it, rebuilt `build/stress` under it; run again.
* `java/stress/kill-restart.sh 200`: KILL RESTART OK: 200 kills and 9
  exits in 313 s, seed 20261127.
* `java/stress/flush-order.sh`: NATIVE FLUSH ORDER OK: 4 writes, 9
  successful file F_FULLFSYNC, 11 successful directory F_FULLFSYNC (12
  with a force per file), 2 deletions, at most 2 in a batch; FLUSH PROBE
  OK.
* `probes/BackupGap.java`: BACKUP GAP OK (5.3, case 5).

#### 5.8. The figure

One run, indicative only, as the machine was not quiet; a measured
comparison waits for a quiet run. `ReclaimCost` as in section 1, with
no rate limit, from `java/`:

    java -Xmx8g -Ddisk=1 -Dlive=20000000 -cp build/bergdb.jar:build/stress bergdb.core.ReclaimCost

On F53, 2026-11-27 17:03, the branch's build, beside this branch's
`level3.sh` (its unit tests) and other sessions' work, load about 9:
110,462 transactions a second (section 1: 63,000 to 68,000 with a force
per file, 102,000 to 109,000 with the batch); the disk / the stream
kept, mean 1.134 (max 1.631); the files that end before fp and are not
deleted, mean 0.145 of the stream kept, of them taken off by the
storage's cut and waiting for its thread 0.013; 28.1 files on average.
So C writes as fast as B and keeps B's disk (section 1's batch: 1.10 to
1.15, 0.11 to 0.17, 26 to 30 files): the deletes no longer lag.

#### 5.9. 031-06's landing

A test merge (`git merge-tree`) of this branch with the branch
`031-06-landing` of the clone c317, at its commit `d3d9dce3`, has one
conflict, in the log at the end of 028's index (`items/028-todo/
readme.md`), where both add an entry: keep both. No code is merged by
hand: the landing does not
touch `FileStream`, `RecoverableStream`, `AppendOnlyStream`, the
power-loss tester or `flush-order.sh`; the check of 5.1 goes into the
landing's `initFromDb(StoredTrans last)` unchanged, before its own
lines; `Db.start`'s catch, `NodeStream` and 027-03 merge. To check after
the merge: the landing's start reads nothing before the cut (its
restarts on `CutStream` in level 3 check it), and the gates of 5.7. The
landing's uncommitted change to `Db.java` in c317 was not seen.

#### 5.10. For Frans

1. **Files before a gap that are no leftovers** (5.3, case 8). As
   built, the start of a whole database after the gap deletes them,
   where the open refused before. Options: (a) as built; (b) delete a
   leftover only if its first meta block (every file begins at one) is
   valid for this database, else refuse; with 028-67's C1, built in
   031-06's landing, a block is valid only with the database's ID, so
   (b) is a read of one block a leftover at the start's cut. It does not
   guard against an older copy of the same database. Recommendation:
   (b), after 031-06's landing, as a small follow-up; (a) until then.
2. **Land C** for 2026.7, in place of A. Recommendation: yes, after a
   timing run on a quiet machine confirms the speed (`ReclaimCost` with
   `disk=1`, 5.8's command, against `main`), with `java/night.sh`
   before the release as usual; C does not conflict with 031-06's
   landing and can land before or after it.

State, 2026-11-27, 17:14: C is built on the branch `028-66c` of the
clone c66c, two commits on `main` at `dd62fc27`, not pushed, and passes
the gates of 5.7; `main` keeps A. Sound as designed (5.2 to 5.4). Left:
Frans's decision to land it (5.10), and question 1; on landing, a timing
run on a quiet machine against `main`.


### 6. Built: C on main with Frans's rule

Built 2026-11-27 by an agent of lead-1127, on the branch
`028-66-c-rule` of a clone of `main` at `734f05a2` (c66d), not pushed;
for the lead's review and the timing run of Frans's decision 2
(section 4). Not marked done: the timing run, the review and the
landing are open.

#### 6.1. The port

The two commits of the branch `028-66c` (section 5) apply to `main` of
2026-11-27 without a change by hand, as 5.9 planned: `main`'s
`RecoverableStream` walks the tail before it writes (028-67, C1), and
the refusals of a stream that lacks bytes (5.1) come before the walk;
`Reclaim.initFromDb`'s check of the first position comes before
031-06's lines of `a`; `FileStream`, the power-loss tester,
`AppendOnlyStream` and `flush-order.sh`'s validator had not changed on
`main`. The only conflict was the log of 028's index, where both sides
added an entry. The port is its own commit; the rule is the next one,
and C does not land without it (Frans's decision 1).

#### 6.2. The rule

Frans's decision 1 (2026-11-27, 17:26), with 028-67's check as it is on
`main` (a meta block holds its own position at offset 46 and the
database ID at offset 24, meta version 156):

* What: a file before a gap is deleted only if its first meta block,
  the first whole block at or after its start (every file that
  `FileStream` makes begins at one), is of this version, valid (its
  last byte), holds its own position and the database ID of the
  stream's first block. Otherwise the start is refused before anything
  is written or deleted, with a `StreamIoException` whose cause is a
  `BadDirStateException`: it names the file, what its block holds (or
  that it holds none), the gap, and the way out, to move the files
  before the gap out of the directory and keep them.
* When: at every start, in `RecoverableStream.recover()`, after the
  last valid meta block is read (which gives the database ID) and
  before the walk of the tail and recovery's writes.
* By whom: `AppendOnlyStream.checkLeftovers(LeftoverCheck)`, a default
  method that holds none; `BufferedStream` and `StorageManager` pass it
  on; `FileStream` gives each file before the gap, oldest first, with a
  reader of its bytes on a channel of its own, and throws the refusal;
  `RecoverableStream.leftoverProblem` checks the block. `FileStream`
  deletes no leftover before a call that found them all to be the
  stream's own, so a cut cannot delete an unchecked or a refused one,
  also under a wrapper that does not pass the call on (the leftovers
  then stay).
* How it is checked: the tests of 6.3; the traces of the power-loss
  model, whose images with a gap must start, which they do only if the
  check passes for the database's own leftovers.

An example, another database's file put at 0 before a gap (from 200,000
to 600,000): "The file 00000000000000.bergdb, before a gap in the
stream's files, is not the database's own: its first meta block, at 0,
holds the database ID 4343..., and this database's is 7dee...: another
database's. At its open the stream's directory D had a gap in its
files: none held the bytes from 200000 to 600000, ... The files before a
gap are deleted only if each one is the database's (bergdb 028-66), and
none of them has been; the start, which checks them before it writes,
has written nothing. To start the database from the files after the
gap, move the files before the gap out of the directory, and keep them:
they may be another database's."

Not refused, as 5.10 said: an older copy of a file of the same
database, whose blocks hold the same ID and their own positions; the
start deletes it. Since the rule, section 5.3's case 8 is refused: a
file before the gap that is not the database's is no longer deleted.

#### 6.3. The tests

* `FileStreamPowerLossTester.testStartDeletesTheDatabasesFileBeforeAGap`:
  the database's first file, kept before a cut deleted it and put back
  before a gap, is checked and deleted by the start's cut; every key
  reads as before; no gap after.
* `FileStreamPowerLossTester.testStartRefusesAFileBeforeAGapThatIsNotTheDatabases`
  (in place of `testStartDeletesAFileBeforeAGap`): refused, the files
  compared byte for byte after each start, for another database's first
  file (another ID), the database's own first file with its block of
  version 155, with its last byte damaged, with its position damaged, a
  file of zeros, and a file of 100,000 bytes at 100,000, which holds no
  whole block; then, the file moved out, the database starts and reads
  as before.
* `RecoverableStream.Tester.testLeftoverProblem`: each branch of the
  block's check, also a piece that begins between two blocks, and that
  it reads the block only.
* `FileStream.testRestartMissingFile`: a cut at the first position
  deletes no unchecked leftover, nor one that a check refused (the
  refusal names the file, what the check found, the gap and the way
  out); after a check that passed, whose reader reads the file's bytes
  and no more, it does. `testGapsAtOpen`: the check gets the three
  leftovers oldest first. `FileStreamPowerLossTester.
  testRecoveryAfterEverySubsetOfABatch` checks before it cuts.
* The power-loss cases of section 5 as before: every subset of a batch
  (`testRecoveryAfterEverySubsetOfABatch`), the unordered deletes
  (`testUnorderedUnforcedDeletionsLeaveAGapThatOpens`), the traces'
  images with a gap in level 3, each started through the check;
  `testStartRefusesAStreamThatLacksBytes`; the BackupGap probe (6.4).

#### 6.4. The gates

On F53, 2026-11-27, 22:00 to 22:45, in the clone c66d (one level script
at a time in a tree, a second tree for the other runs), beside
`java/night.sh` and another session's level 2 and 3 (load 18 to 30):

* `java/before-commit.sh`: BEFORE COMMIT OK (113 s) on the port's commit
  alone; BEFORE COMMIT OK (117 s; unit 1,749 tests, f 96) on the rule's
  commit.
* `java/stress/level2.sh`: LEVEL 2 OK.
* `java/stress/level3.sh`: LEVEL 3 OK: every step; the power-loss
  stage POWERLOSS OK, 8 seeds, 488 cold recoveries, without per-append
  forces 496, negative controls caught; its 16 traces made batches of
  up to 3 files and 3 to 7 images with a gap each, 77 in all, every one
  started through the rule's check, its files before the gap deleted;
  conformance reclaim 40 traces and crash 15, TRACECHECK OK;
  InterruptStress 60 s.
* `java/stress/level4.sh quick`: LEVEL 4 OK.
* `java/stress/kill-restart.sh 200`: KILL RESTART OK: 200 kills and 9
  exits in 217 s, seed 20261127.
* `java/stress/flush-order.sh`: NATIVE FLUSH ORDER OK: 4 writes, 9
  successful file F_FULLFSYNC, 11 successful directory F_FULLFSYNC, 2
  deletions, at most 2 in a batch; FLUSH PROBE OK.
* [probes/BackupGap.java](probes/BackupGap.java), 100 copies: whole 45;
  with a gap, started 5, refused 36; without their first files, started
  14, refused 0; BACKUP GAP OK. Every refusal said that the stream lacks
  bytes, none was the rule's: a copy's files before a gap are the
  database's. More copies had a gap than in 5.3 (41 against 15), on a
  machine about twice as loaded.
* 031-06's `probes/sweep.sh`: SWEEP DONE, 0 different in each of its 63
  lines (crash, pre and stop at every record, restarts in the
  continuation, torn records).
* 031-06's `probes/faults.sh`: FAULTS DONE, bad 0 in each of its 42
  lines.

#### 6.5. The timing comparison

Frans's decision 2 asks for a timing run on a quiet machine against
`main`. Section 1's measurement as an A/B of the two builds:
[probes/ab-reclaimcost.sh](probes/ab-reclaimcost.sh), `ReclaimCost` on
disk (`disk=1`, `live=20000000`, no rate limit), the reference and the
candidate in ABBA order, 2 rounds (4 runs each), with each run's
`STEADY`, `DISK` and `DISK PARTS` lines and the medians at the end.
REF is a build of `main` and CAND one of the branch: each a tree's
`java/build` after `java/build.sh`. From the repository's root, the
builds made first, with nothing else running (no `night.sh`, level
script, build or other session's tests):

    git worktree add ../c66-ref main && (cd ../c66-ref && sh java/build.sh)
    git worktree add ../c66-cand 028-66-c-rule && (cd ../c66-cand && sh java/build.sh)
    sh items/028-todo/66-cut-deletes-lag/probes/ab-reclaimcost.sh \
        ../c66-ref/java/build ../c66-cand/java/build OUT

About a minute a run, 8 runs (an estimate). The script was tried with
`LIVE=2000000 ROUNDS=1` on a loaded F53 (load 27 to 30), its plumbing
only: 4 runs, RECLAIMCOST OK each, the medians printed; not a
measurement.

C's effect is in the medians: transactions a second (section 1 with a
force per file, `main`: 63,000 to 68,000; with the batch: 102,000 to
110,000), the disk over the stream kept (1.43 to 1.58 against 1.10 to
1.15), the files that end before fp and are not yet deleted (0.45 to
0.59 of the stream kept against 0.11 to 0.17), of them those that the
storage's cut took off and its thread has not deleted (0.33 to 0.45
against at most 0.02), and the files on disk (54 to 63 against 26 to
30). The figures of section 1 and 5.8 came from a loaded F53. The rule
adds one read of 128 bytes a leftover at a start, and nothing to a
cut.

`java/timing.sh` compares the tree with the last release, not with
`main`; run on the branch, it checks that C costs nothing elsewhere
(CORE, the pause probe, `performance.sh ab` with the release suite,
whose `w-uni-100-fin`, `r-100-fin` and `w10m-fin` make cuts on a
`FileStream`), and its figures can be set beside the timing run on
`main` of 2026-11-27, 17:16 (006-37). Its `CAND` and `REF` take two
builds for core and pauses only.

#### 6.6. What is left

* The timing run of 6.5 on a quiet machine (Frans's decision 2), and
  027-13's figure from it in place of 5.8's indicative one.
* The review of the branch, then the landing in place of A for 2026.7;
  `java/night.sh` before the release as usual.
* 028-73 (the sizes of new files) waits for Frans; C does not change
  file sizes.

Log
---

2026-11-26. Registered by lead-1126, from 028-62's measurement.

2026-11-26. Measured by an agent of lead-1126 (clone c66, branch
`028-66`): the lag at 10 to 100 MB/s and with no limit, the quarter,
the tenth and a batch delete with one directory force; the batch keeps
the disk at 1.03 to 1.05 of the stream, and the writer as fast as with
the quarter, but breaks 011-07's order of deletes under the power-loss
model: not landed, options A to C for Frans. `ReclaimCost` takes
`rate=X`.

2026-11-27. Option C designed and built by an agent of lead-1127 (clone
c66c, branch `028-66c`, not pushed), from Frans's principle of the same
day: the cut's deletes a batch with one directory force; `FileStream`'s
open takes a gap in its files, the stream from the file after it; a
start refuses a stream whose first position is after reclaim's cut, and
else its cut deletes the files before the gap; the power-loss model
keeps any subset of unforced deletes. Sound (section 5); the gates of
5.7 pass; for Frans: land C, and question 1 (5.10).

2026-11-27. Frans decided (17:26): C with the rule of the files before a
gap (question 1, option b), and C in place of A for 2026.7 after a quiet
timing run against `main` and a review (section 4).

2026-11-27. C ported onto `main` at `734f05a2` and Frans's rule built by
an agent of lead-1127 (clone c66d, branch `028-66-c-rule`, not pushed):
a start deletes the files before a gap only if each one's first meta
block is the database's (028-67's position and ID), and else refuses
before it writes or deletes; the tests and the gates of section 6; the
A/B of `ReclaimCost` for the timing run (6.5). Left: the timing run, the
review, the landing.
