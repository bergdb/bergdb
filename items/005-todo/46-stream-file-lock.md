005-46. A read of the stream's last file waits for the writer's fsync
=====================================================================

Status: open. Kind: fix. Created 2026-10-26.

Found in item 009's measurements
([009-03](../009-handles/03-measurements.md), sections 4 and 7), by Claude
(Opus 5.5, Claude Code), during Frans's unattended run of 009.


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


Done when
---------

A reader of the last file does not wait for the writer's `fsync`: a test
with a slow forcing `FileStreamIo`, the pause probe on s1 again, and the
level 3 gates (reclaim's cut and its delete of files) pass.
