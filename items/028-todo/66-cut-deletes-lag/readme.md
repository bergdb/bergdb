028-66. Investigate: the cut's deletes lag behind a fast writer
================================================================

Status: open. Kind: Investigate. Frans: decision (B or not; section 4).
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
