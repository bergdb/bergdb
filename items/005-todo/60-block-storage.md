005-60. Investigate: the stream on a block device, without a file system
=======================================================================

Status: open. Kind: investigate. Created 2026-10-27.

Frans's idea, 2026-10-27, added as an entry at his request, by Claude
(Opus 5.5, Claude Code). A place to collect what is found; nothing is
started.


The idea
--------

In Frans's words (2026-10-27): "I wonder about block storage. For Java, I
guess we cannot by-pass the filesystem. Or can we? [...] investigating the
feasibility of using block-based storage instead of a file system to store
the BergDB data. Since it is purely append-only, the mapping from stream to
blocks seem simple. I guess we would just write in a round-robin fashion.
Fixed max size. Having a variable retention period is one option.
Everything is stored until space is needed again. This item should check
if this is possible in Java, but it is also of interest to consider how
this could work in a Linux device and C or C++ code. A clone."

So: the stream on a raw block device (a disk, a partition, an SSD's
namespace, raw flash), with no file system under it. The device is a ring
of a fixed size: stream position p is at device offset H + (p mod C), where
H is a small header and C the ring's capacity. The writer goes round and
round; the front of the stream is given up only when the ring needs the
room. The retention is then by space, not by time: the history reaches as
far back as the ring holds, and how far that is in time depends on how fast
the database writes.


Today
-----

* The storage is an `AppendOnlyStream` (`java/src/bergdb/stream/`):
  `append`, `read` at a position, `getLength`, `getFirstPos`, `pretruncate`
  (cut the front), `seekFirstPos`, `close`; one writer, many readers. A
  ring on a block device would be one more implementation, beside
  `FileStream` and `MemoryStream`, and nothing above it needs to know.
* `FileStream` keeps the stream in files of 200 kB and more in a
  directory; a cut deletes whole files from the front, and an append
  forces the file (`FileChannel.force(true)`: `F_FULLFSYNC` on macOS,
  `fsync` on Linux; 005-47). Its file system seam is `FileStreamIo`.
* Recovery: a record starts with its size and ends with a commit byte, and
  a meta block of 128 bytes sits at every multiple of 200,000 bytes, so a
  start finds the last whole record without reading the whole stream
  (`RecoverableStream`; 006-08, section 6.5). A meta block holds the
  position of the last whole transaction before it (`lastTrans`,
  `MetaBlock`). With files, the stream's end is the last file's length; a
  device has no such length.
* Reclaim (docs/levels.md, section 6) cuts the front by time: it rewrites
  the live values stored before the cut point, and the cut waits until
  they are older than the retain duration R. The default is to retain
  forever. A ring needs the cut by space.
* 006-08, section 6.5, had the same thought for a C clone on raw flash: the
  stream as a ring of erase blocks, each erased once a round, which levels
  the wear without a layer for it; "an idea, not tried". 005-13 left "a
  storage design for SSDs and flash" out of scope (Frans, 2026-10-20).
* BergDB builds with `--release 17`.


Questions
---------

1. **Java.** Can a JVM read, write and force a raw block device, and how
   well? To check, on Linux: opening a device (`/dev/nvme0n1p3`,
   `/dev/sdb`) with `FileChannel`, and the rights it needs (the group
   `disk`, or root); the device's size (`FileChannel.size()` on a block
   device, or `/sys/block/`); direct I/O with
   `com.sun.nio.file.ExtendedOpenOption.DIRECT` (JDK 10 and later), with
   buffers aligned to the block size; what `force` does on a device (a
   flush of the drive's cache?); the Foreign Function & Memory API for
   what the JDK lacks (`ioctl`, `fdatasync`, `io_uring`), which is final
   only from Java 22, so not with `--release 17`. macOS (`/dev/rdiskN`,
   root) and Windows (`\\.\PhysicalDriveN`) only as far as they matter.
2. **The tail sector.** A device writes whole sectors (512 B or 4 KB). A
   flush that ends inside a sector means that the next append writes the
   sector again, with bytes that are already durable, and a power loss
   during that write may tear the sector and lose them. Options: pad each
   flush to a sector boundary (the padding outside the stream, so that the
   stream's bytes stay the same, P2), rely on the device's atomic write
   unit (NVMe's AWUPF), or write the tail sector to alternating places.
   Which, and at what cost in space and writes?
3. **Recovery.** How a start finds the stream's first position and its end
   without files: a header (written when, and how atomically?), then a scan
   forward from a known position. Past the end lie the bytes of the
   previous round, which look like records too. Do the meta blocks'
   `lastTrans` tell a round from the one before, or does the ring need a
   frame of its own (a round number per sector)? And a fault model of a
   device, as 011-07 has one for a file system.
4. **Capacity and retention.** With a fixed C, the live part of the stream
   (first position to end) must stay below C, with room for the startup
   section and for reclaim's work. Reclaim would start an iteration when
   the free room falls below a mark; what happens when the ring is full
   anyway: the writer waits, or the database refuses writes? What C must
   be for a given amount of live data (reclaim's cost, 011-04), how far
   back the history then reaches, and how a retain duration and a space
   limit go together (a floor of history, or one or the other). Retention
   by space needs no device: it could be tried first as a size limit for
   `FileStream`.
5. **What it gains.** Measured, not assumed, on the same SSD against
   `FileStream` on ext4 or XFS: a durable commit's latency (a force of the
   device against a force of a file), throughput, the cost of a cut (no
   file deletes; before 005-46 a cut of 57 files took 309 ms), the longest
   waits. With direct I/O the OS's cache is gone, and today the reads of
   evicted nodes are often served from it (009-03's ScaleBench C). And
   what is lost: tools that copy and inspect files, backups, and the setup
   of a device, against P10 (no administration).
6. **Linux and a C or C++ clone.** How a clone on a Linux device would do
   it: `open` with `O_DIRECT`, `pwrite` and `fdatasync`, or `io_uring`;
   user-space NVMe (SPDK) on a server; zoned storage (NVMe ZNS,
   host-managed SMR), whose zones are written append-only and reset whole,
   which is the ring in hardware; raw flash with no OS (006-08, section
   6.5), where the ring would level the wear. Which of these suits the
   targets of 006-08's clone?
7. **Prior art.** Systems that left the file system for a raw device, and
   why, and the arguments against: Ceph's BlueStore ("File Systems Unfit as
   Distributed Storage Backends", SOSP 2019), Aerospike's log-structured
   storage on raw SSDs, whose defragmenter does what reclaim does, Oracle's
   raw devices and ASM.


Principles
----------

P2: the stream's bytes stay the same; the ring, the header and any padding
lie beneath the stream. P5: a start finds the end in a bounded time. P1: a
full ring must not stop the world; the writer waits for reclaim only in
bounded steps, if at all. P10: a raw device needs setup (a partition,
rights), so it would be an option for those who want it, not the default.
P11: the simple ring first.


Done when
---------

A report, a subitem of this entry, answers questions 1 to 7 as far as
reading and probes can: a Java probe that writes, forces, reads and
restarts a stream on a block device on Linux; a sketch of the ring's
layout, recovery and tail sector; the measurements of question 5 if a
device can be had; how a C or C++ clone would do it; and a recommendation:
an item of its own, later, or dropped. Nothing goes into `java/`.


First step
----------

Reading: the JDK on block devices (question 1), the prior art (question 7),
and `AppendOnlyStream`, `FileStream` and `RecoverableStream` for how a
start finds the stream's ends today. Then a probe on a Linux machine with a
device to spare. Which machine is a question for Frans: s1 has one disk,
but a loop device there is enough to test function (a loop device is
backed by a file, so not for timing).


Size and order
--------------

M to L. After 006-09's unattended work; independent of 007 and 009.


Notes
-----

What is found, dated, until the report is written.

2026-10-27. Created; nothing read or run beyond the repo's own documents
cited above.

2026-10-27. The tail sector (question 2), with files today; Frans asked how
file systems do it. A force writes whole blocks: an append of a few hundred
bytes and a force make the file system write the 4 KiB block that holds
them, and, as the file's length changes, a commit of its journal (ext4,
XFS). A block that a flush leaves part full is written again, in place, at
the next flush, with the bytes already durable in it; with the 20 ms buffer
and small syncing commits, that can be ten times or more for one block. So
the stream is append-only as a file, not on the device.

It is safe as long as the device writes each sector whole or not at all.
The old and the new version of the tail block agree on every byte that was
durable and differ only past the old end, so even a block torn at sector
boundaries keeps those bytes. What breaks it is damage within a sector: a
hard disk's sector cut off mid-write can read as an error, and SSDs without
power-loss protection have shown corrupt and torn sectors under power
faults ("Understanding the Robustness of SSDs under Power Fault", FAST
2013). ext4 in its default mode (`data=ordered`) and XFS journal only
metadata, so they do not protect the tail block; ext4's `data=journal`
writes the data twice and does; copy-on-write file systems (ZFS, btrfs)
write the new block elsewhere and keep the old one until their commit.

BergDB assumes it. 011-07, "Limits and next work": the result "assumes
successful OS forces persist the requested data and namespace, and later
appends do not corrupt previously forced bytes", and does not establish
behavior with "torn previously durable sectors". `FileStreamPowerLossTester`
loses at most the unforced tail and keeps an arbitrary prefix of it. So a
ring on a device has the same problem as files have today, no worse; it
only becomes BergDB's own to solve.

Leads, from memory, to check against the sources: InnoDB's redo log is
circular in fixed-size files, written in 512-byte blocks, each with a
header that holds its number and a checksum, so a rewrite of the last block
is one sector, and a stale block of the round before is told by its number
(question 3). PostgreSQL's WAL pages carry their own WAL address
(`xlp_pageaddr`), which tells the old pages of a recycled segment from new
ones. SQLite's "powersafe overwrite" (sqlite.org/psow.html) names this very
assumption; without it, SQLite pads a WAL commit to the end of the sector.

A middle way, for questions 4 and 5 and P10: the ring in one preallocated
file, written once round, on an ordinary file system. An overwrite of
written blocks changes no metadata, so `force(false)` (`fdatasync` on
Linux) writes the data only, with no journal commit. Java needs no rights
for it, and it runs on macOS. The recovery questions are a device's: no
file length tells the end. Oracle's online redo logs are such fixed files,
used round-robin.
