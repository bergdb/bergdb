005-46. A read of the stream's last file waits for the writer's fsync
=====================================================================

Status: open. Kind: fix. Created 2026-10-26.

Found in item 009's measurements
([009-03](../009-handles/03-measurements.md), sections 4 and 7), by Claude
(Opus 5.5, Claude Code), during Frans's unattended run of 009.

Item 009's target 2 waits for this item (009-01): no get or commit stopped
for more than about 20 ms by BergDB's own code, the collector's pauses not
counted (Frans, 2026-10-27). Both waits below are BergDB's own.


The fault
---------

`FileStream.DbFile.read` and `DbFile.append` are both `synchronized` on the
file, and `append` writes and then forces the file (`io.forceFile`, an
`fsync`) inside that monitor. So a reader that needs a node from the last
file of the stream, the one the writer appends to, waits for the writer's
whole append and its `fsync`.

On F53 an `fsync` is short and it does not show. On s1 (a virtual disk) it
can take seconds: with handles (009, step 3d), where no sweep stops the
readers any more, the pause probe's longest waits on s1 are these, 1.4 to
2.7 s for a get and for the commit beside it, with no collection, safepoint
or eviction batch under them (009-03, section 4). They were there before 009
too, hidden among 2026.1's sweeps of 0.7 to 2.5 s.

It is a stop of its own: every reader that loads from the last file, at any
level of the index, waits for the writer's I/O.


The cut
-------

Added 2026-10-27 by Claude (Opus 5.5, Claude Code), from the soaks of
[009-04](../009-handles/04-shenandoah-degenerated.md), section 7.3: a second
wait of the same kind. `FileStream.pretruncate`, reclaim's physical cut, is
`synchronized` on the stream and deletes the files before the cut one by
one, forcing the directory after each (so that a crash cannot keep an
older file and lose a newer one). Every `FileStream.read` takes the same
monitor to find its file (`findFile`), so every read from the stream waits
for the whole cut.

In P4's soak on F53, the cuts of 11, 2 and 4 files took 88 to 171 ms, 17
to 31 ms and 46 to 96 ms, about 8 to 24 ms a file, and they were the
soak's slowest commits under ZGC and under Shenandoah alike; the longest
gets and scans matched them. On a disk like s1's, where a force can take
seconds, a cut would stop the readers longer.


Options
-------

* **Positional reads without the monitor:** `FileChannel.read(buffer,
  position)` is safe for concurrent use and needs no seek, so `read` can
  run beside an `append`. What it must still get right: the file length a
  read may see (written by `append`; volatile, or read under a short lock),
  a read that meets a file that `pretruncate` closed and deleted (today
  `ReadBelowFirstPosException`, 2026-10-13; with a channel, a
  `ClosedChannelException` to map), and `FileStreamIo`, the power-loss
  tests' hook, which reads do not use today.
* **The `fsync` outside the file's monitor:** append under the monitor,
  force after it. Readers then wait for the write only; the order of the
  write and the commit byte (005-44) must stay.
* **The cut's deletes outside the stream's monitor:** take the files off
  the stream's list under the monitor, so that new reads see the new first
  position, and delete them and force the directory after it, in the same
  order. A read that still holds one of the files gets
  `ReadBelowFirstPosException` from `DbFile.read`, as today when it meets a
  deleted file.


Done when
---------

A reader of the last file does not wait for the writer's `fsync`, and a
reader does not wait for a cut's deletes: a test with a slow forcing
`FileStreamIo`, the pause probe on s1 again, P4's soak (its cuts), and the
level 3 gates (reclaim's cut and its delete of files) pass.
