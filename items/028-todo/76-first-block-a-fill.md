028-76. Fix and decide: a stream whose first meta block is recovery's fill
========================================================================

Status: fixed on `main` for the stream's first block; the files before a
gap decided (a). Kind: Fix, then Decide. Frans: decided.
Created 2026-11-28 by Frans Lundberg.

What: `week.sh` of 2026-11-28 on `main` at `8a0897cf` failed its step
apps-kill-cc: the Kill app (seed 2078503, database 4, node size 62,
retain 1000), after its 30th kill, could not start the database: "Could
not find *any* valid meta block. At least the very first meta block must
be valid in a db stream. The stream begins at 800000 ..."; nothing was
written. The database was sound: nothing was lost or written out of
order.

How: an earlier kill of one of the database's children ended the stream
exactly at 800,000, a meta block's position; the next start filled that
position as recovery does (005-27): the magic bytes, version 156 and
zeros, last byte 0, not a valid block. Later blocks, from 1,000,000 on,
were valid and held their own positions and the database's ID. A cut of
reclaim then deleted the files before 800,000, so the fill became the
stream's first block. Since 028-67's C3 (`b0aac3a9`, 2026-11-27), a start
read only the stream's first block (`RecoverableStream.readFirstMetaBlock`)
and refused when it was not valid. A block of zeros that a kill leaves
inside an aborted record (028-60) can come first in the same way. Every
build from `b0aac3a9` to `8a0897cf` refused the kept copy; 2026.6 has no
such rule (no released bug, 033).

Fixed (2026-11-28, `05bf46e3`, `6f3ef697`, `27267148`): the stream's
first block is the first valid block at or after the stream's first
position; invalid blocks before it are passed over, as the backward
search for the last valid block already does. A first valid block that
does not hold its own position is still refused. A cut stream always
holds one of its own valid blocks after its first position, written
before the cut deleted anything. 027-03, section 6, and 027-11, step 3,
state the rule. Tests that failed before the fix with the week run's
exception: `RecoverableStream.testCutStreamBeginsAtInvalidBlock`
(MemoryStream: the fill and a zero block) and
`FileStreamPowerLossTester.testStartOnACutStreamThatBeginsAtAnInvalidBlock`
(a database on files: a kill at a file's first block, the fill, a cut to
that file, a restart). With the fix the kept copy starts and the Kill
app's check of its records passes. Gates on `b9e45295` and the fix:
`BEFORE COMMIT OK (127 s)`, `LEVEL 3 OK`, the Kill app with seed 2078503
(300 kills, 307 recoveries checked) and three other seeds OK, `APPS OK`
(quick), 031-06's sweep 0 different in 63 lines, faults bad 0 in 42,
`PowerLossTest 1001 12 3000 3` OK.

Open, for Frans: 028-66's rule for the files before a gap (Frans,
2026-11-27, 17:26: such a file is deleted only if its first meta block
is this database's, else the start refuses) meets the same fill. After a
power loss, a leftover file whose first block is recovery's fill makes
the start refuse a sound database (`BadDirStateException`, the way out:
move the files before the gap out of the directory). The first valid
block of the file does not help: a 200,000-byte file holds only that one
block. The options:

* **(a) Keep the rule as it is.** The start refuses, names the file and
  the way out; nothing is lost; a person moves the file. Rare: it needs
  a kill exactly at a file's first block, a later cut of that file, and
  a power loss inside the cut's batch.
* **(b) The fill writes a valid block.** Recovery's fill at a meta block's
  position writes the block's own position and the database's ID (and
  what else a valid block needs), so every block that a start writes is
  identifiable as this database's. Also removes the first-block case at
  its root. A change of the recovery and of the meant content of a fill
  (005-27, 027-03); needs a study of what a valid block's other fields
  hold when no record ends there.
* **(c) Delete a leftover whose first block is a fill when a later file
  of the stream is this database's.** Weaker: a fill holds no ID, so a
  foreign file with a fill at its first block would be deleted.

Recommended: (a) for 2026.7, (b) studied with 031-07's review of the
stream's checks.

Decision: Frans, 2026-11-28, 06:05: (a) for 2026.7.

Note (2026-11-28, from the review of the start path, 033,
`reviews/2026-11-28-start.md`, F5; not a change of the decision):

* The same refusal meets a first block that a kill cut inside (1 to 127
  of its bytes written) and recovery completed: the block then holds the
  database's ID and its position and a last byte of 0, and the message
  says "is not valid, its last byte 0: damaged".
* Option (a)'s "a kill exactly at a file's first block" says too little:
  the kill need not come at one instant. The stream moves to a new file
  between the append that fills the last file and the first append to
  the new one, with the forces of the full file, of the new file and of
  the directory between them (`FileStream.newFile`); a kill of a busy
  writer ends the stream at the file's first block for the time of
  those forces, in each file's writing. `week.sh`'s Kill app met it at
  its 30th kill.
* How often, in the review's `StartChain` (chains of kills, kills
  inside a recovery's writes and power losses in a cut's batch, each
  start on what the fault before left): the decided case 212 times in
  21,000 starts without other bytes (87 in 8,000 with files of 200 kB,
  33 in 7,000 with files of 200 kB to 5 MB, 92 in 6,000 with per-append
  forcing off), and no other refusal. The probe makes the kills at
  chosen positions, a file's start among them, and takes files off as a
  power loss in a cut's batch does; the figure is the probe's, not a
  rate of use.

Found by: `week.sh` of 2026-11-28 (java/build/week, apps-kill-cc), the
Kill app of `java/stress/apps.sh`'s kill set.


Log
---

2026-11-28. Registered by lead-1127 from `week.sh`'s failure; the first
block fixed on `main` (`05bf46e3`..`27267148`) by an agent of lead-1127;
the files before a gap left for Frans.

2026-11-28. Frans decided (a) for 2026.7 (06:05).

2026-11-28. A note under the decision from the review of the start
path (F5): the refusal also meets a first block cut inside and
completed; the kill lands at a file's first block for the time of the
file switch's forces; `StartChain` met the decided case 212 times in
21,000 starts.
