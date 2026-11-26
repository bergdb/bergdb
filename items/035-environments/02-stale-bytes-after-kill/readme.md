# 035-02. A deleted file's bytes within a file's length after a kill

Created 2026-11-26 by Frans Lundberg. Status: open.

Whether a write that a SIGKILL cuts on APFS can leave a deleted file's
bytes within the file's length, not zeros, on F53's internal SSD as on
035-01's disk images and RAM disks; how often; whether s1 (Linux, ext4)
does; and what a start of BergDB does with such bytes in its last
stream file, with the options for a 028 entry.


## 1. The question

035-01 found that on APFS a write cut by a SIGKILL can leave a dropped
piece of the write (1 to 4 MiB, aligned to the write's first page)
within the file's length. On an APFS disk image and an APFS RAM disk, 7
such cut files held a deleted file's old bytes in that piece, not zeros
(035-01, section 7). For BergDB this is the worst case: the deleted file
is an earlier stream file, whose records and meta blocks, read inside
the last file's length, a start could take as its own (wrong data, S1),
and none of 028-60's options B1 to B3 covers it (035-01, section 10).

* Does F53's internal SSD (APFS) show a deleted file's bytes in a cut
  write, or only zeros? It matters most: BergDB runs there.
* Which writes: the first write of a new file only, or later appends
  too? Which pieces of the write?
* Whose bytes: the file deleted just before, an older one, another
  process's?
* Does s1 (ext4) ever show them?
* What does a start of BergDB do with an older stream file's records
  and meta blocks inside the last file's length?


## 2. What is known

From 035-01 (2026-11-26):

* On APFS (internal SSD, disk image, RAM disk) a kill that finds a write
  of more than one page can end it with the pieces before the cut piece
  right and wrong bytes from a page boundary in the cut piece to the
  file's length L, a page boundary inside that piece, short of the
  write's end (035-01, sections 6.1 and 9). The piece is 1 MiB on the
  internal SSD, 2 MiB on the RAM disk, 4 MiB on the disk image.
* On the internal SSD, 35 cut files, all zeros; 3 of them were the first
  write of a new file cut in a later piece (the third, fourth and sixth).
* On the RAM disk and the disk image, 18 cut files; 7 held the fill byte
  of an earlier write of a file deleted before (each the first write of
  a new file, cut in its second or third piece); the 11 cut in their
  first piece read as zeros.
* 035-01's probe fills each write with one byte value, so an old byte
  names only a write's sequence number modulo 255, not its file and
  offset.
* On s1 (ext4) and HFS+, no zeros and no wrong byte: a kill leaves a
  prefix of the write or nothing.


## 3. The study

1. A probe (one Java file, no BergDB code, in `probes/`) whose every 4
   KiB block of every file carries a tag: a marker, the run, the trial,
   the file's id and the block's offset in its file. A child first
   writes and forces prepared files and deletes them, then creates new
   files and appends (sizes 64 KiB to 8 MiB; force by
   `FileChannel.force(true)`, F_FULLFSYNC, by fsync, or none, as
   035-01); the parent kills it at random, or timed to the first write
   of a new file. For every cut write, each 4 KiB block within the
   length is classified: right, zeros, a tagged block of another file
   (whose file and offset), or other bytes.
2. F53's internal SSD, the case that matters most: hundreds of cut first
   writes of a new file, and later appends.
3. For comparison: an APFS disk image and an APFS RAM disk on F53, and
   s1 (ext4).
4. For BergDB, by reading the code and, where cheap, a throwaway test
   outside `java/`: whether a record or a meta block carries anything
   that ties it to its stream position or its file, and what a start
   does with an older file's records and meta blocks inside the last
   file's length (`RecoverableStream`'s recovery, `FileStream`).
5. The options for BergDB, as a draft for a 028 entry.


## 4. The probes

### 4.1. StaleBytesProbe

[probes/StaleBytesProbe.java](probes/StaleBytesProbe.java), from
035-01's `ZeroTailProbe` (2026-11-26); its header gives the options.

* **Tags.** Every 4 KiB block of every file that the child writes
  begins with 32 bytes: the marker `STALE035`, the run's nonce, the
  trial, the file's id, the block's offset in its file and a check of
  these. The other bytes of a write are its fill byte, 1 + seq % 255.
  So every byte that the probe ever wrote names its run, trial, file
  and offset, and a block read in another file says whose it is.
* **The child** first writes prepared files (`prep=N:BYTES`, ids 1000
  and up), forces each with `FileChannel.force(true)` and deletes them;
  then, after an optional pause, it opens file 0 and appends as
  035-01's child: a side log line `W seq start size` before each write,
  `w` after it returns, `f` after its force (`force=1`: F_FULLFSYNC, as
  FileStream's hard sync; `2`: fsync; `0`: none). At a cap it opens the
  next file and deletes the last, before the next file's first write
  (035-01's order) or, with `lag=1`, after it.
* **The kill.** Before each write the child prints `S seq start file`
  on its standard output. With `target=first:A:B` the parent waits for
  the line of the first write of file k (k from A to B), then a random
  0 to 2,000 µs (a busy wait), and kills the child with
  `Process.destroyForcibly()` (SIGKILL); with `target=seq:A:B` the same
  for write seq s; with `target=any` after a random 20 to 400 ms, as
  035-01.
* **The analysis.** The parent compares every byte of the last file
  with what the log says was written there. From the first wrong byte
  to the length, each 4 KiB block is classified: zero, tagged (a valid
  tag of another file: this trial's, an earlier trial's, another
  run's, with its file, offset and the offset's difference, delta),
  single (one byte repeated) or other (its entropy is kept, not its
  bytes). A trial's class is complete, none or prefix as in 035-01, or,
  with a wrong byte, stale (a tagged block), single, other or zeros.
  For a cut file the parent then forces the file and keeps its
  allocated bytes (stat(1)'s `st_blocks` × 512), and with `phys` the
  device blocks of its wrong range against those of the prepared files
  and of the files of the last 500 trials. The earlier versions (the
  runs named `i` to `m`, and the RAM disk's first) lack some of these;
  the first two took the first block of a run of another file's tagged
  blocks for other bytes (the tag's marker matched), a mistake that no
  run on the internal SSD met.
* **A kill that found a write** is one whose log ends in `W`, as in
  035-01; "first" is the first write of a file (start 0), "later" the
  others. A cut write is one that ended as prefix, zeros, stale, single
  or other.
* **The runs' names**: `first0`, the kill timed to the first write of
  file 0 in a new process, after a prepared file of 1 to 8 MiB deleted
  and a pause of 0 to 100 ms (or no prepared file); `first1` and
  `first3`, to the first write of files 1 to 3 or 3 to 6, in files of
  16 MiB; `later`, to writes 2 to 14, in files of 64 MiB; `any`,
  035-01's random kill, in files of 16 MiB. F, S and N: `force=1`, `2`
  and `0`; `lag`: `lag=1`; `fdel`: the parent forces each file before
  it deletes it. Sizes 64 KiB to 8 MiB (`r:65536:8388608`) unless said.


### 4.2. EfaultProbe and the helpers

* **[probes/EfaultProbe.java](probes/EfaultProbe.java)**: a write that
  fails inside its copy, without a kill. Each try writes, forces and
  deletes a file of 8 MiB of 0x5a; maps a file of 8 MiB of the try's
  own byte value (`MappedByteBuffer`) and truncates it to a random
  cutoff above 1 MiB, a multiple of the page; then writes the whole
  mapping into a new file with `FileChannel.write`, which the kernel
  copies from the mapping until the cutoff, where the copy faults
  (EFAULT). It counts the new file's length and the bytes within it
  that are not the try's value: zeros, 0x5a, other.
* **[probes/efault2.c](probes/efault2.c)** (macOS): the same write from
  an anonymous mapping whose pages from the cutoff on are unmapped, and
  the device's blocks of every file (`F_LOG2PHYS_EXT`): whether the
  wrong range lies in blocks that a deleted file held with its written
  bytes, of the same run or, with a log, of earlier runs.
* **[probes/phys.c](probes/phys.c)** (macOS): a file's extents on its
  device, for `StaleBytesProbe`'s option `phys`.
* C helpers, as the device's blocks are not at hand in Java; the
  probes' rule (035, "Rules") is Java, and `EfaultProbe` keeps to it.


## 5. The environments

* **F53**: as 035-01, section 5: MacBook Pro (MacBookPro18,3), Apple M1
  Pro, 32 GB; macOS 27.0.1 (26A434), Darwin 27.0.0,
  `xnu-13432.1.9~1/RELEASE_ARM64_T6000`; page size 16,384; the data
  volume APFS on the internal SSD (`disk3s1`, APPLE SSD AP1024R, TRIM
  supported; "FileVault: No (Encrypted at rest)"; 4 KiB blocks; about
  385 GiB free of 926); OpenJDK 27.0.1.1 (Homebrew). Beside the probes,
  `java/week.sh` (its conformance steps until about 12:50) and other
  sessions ran: load averages 6 to 27 (`uptime`) during the runs. Two
  to four probes at a time, children at `nice -n 5`.
* **An APFS RAM disk** on F53: `hdiutil attach -nomount ram://1048576`
  (512 MiB), `newfs_apfs`, mounted with `mount_apfs -o nobrowse`,
  detached after its runs; made again the same way for section 7.3.
* **An APFS disk image** on F53: a sparse image of 2 GB on the internal
  SSD (`hdiutil create -type SPARSE -fs APFS`), attached with `hdiutil
  attach -nobrowse -mountpoint`, detached after its runs and deleted.
* **s1, a Linux VPS**: as 035-01, section 5: Ubuntu 26.04 LTS, kernel
  7.0.0-30-generic, x86_64, KVM with 2 virtual CPUs (AMD EPYC-Rome),
  3.8 GB; page size 4,096; ext4 (block size 4,096,
  `rw,relatime,discard,commit=30`) on a virtual disk of 50 GB ("QEMU
  HARDDISK"); Temurin JDK 27.0.1.1+4, unpacked for the probe and
  removed after. Nothing else ran (load average below 0.2 before);
  `nice -n 10`.


## 6. F53: APFS on the internal SSD

### 6.1. Kills

Runs of 2026-11-26, 11:58 to 13:09, two to four at a time, families of
runs with the same kill (section 4); the earlier versions of the probe
(runs named `i` to `m`) kill and write as the last version does.

| runs                              | kill at the write  | trials | first W | cut | later W | cut |
|---|---|---:|---:|---:|---:|---:|
| `first0`, F, prepared file, pause | of file 0          | 25,942 | 21,047 | 51 |     3 |  0 |
| the same, deletes forced          | of file 0          |  8,549 |  7,583 |  0 |     0 |  0 |
| `first0`, F, prepared, no pause   | of file 0          |  1,863 |  1,566 |  0 |     0 |  0 |
| `first0`, F, none, deletes forced | of file 0          |  3,111 |  2,775 |  0 |     0 |  0 |
| `first1`, F, `lag=1`              | first, files 1–3   |  2,525 |  1,258 |  1 |     0 |  0 |
| `first1`, N, `lag=1`              | first, files 1–3   | 16,259 |  5,693 | 11 | 4,136 | 51 |
| `later`, F                        | writes 2 to 14     |  1,681 |     30 |  0 |   785 |  4 |
| all                               |                    | 59,930 | 39,952 | 63 | 4,924 | 55 |

"first W" and "later W": the kills that found the first write of a
file, or a later one (section 4); "cut": those of them that left a
prefix or wrong bytes. "pause": 50 or 100 ms between the prepared
file's delete and file 0; "none": no prepared file; "deletes forced":
the parent forces each file of the trial before it deletes it
(`fdel=1`).

* **63 cut first writes of a new file, none with another file's
  bytes**: 59 zeroed, 4 clean prefixes. Of the 59, 45 were cut in a
  later piece (the wrong bytes from the write's second piece of 1 MiB
  or later on), the case that gave a deleted file's bytes on the RAM
  disk and the image (section 7); 14 in the first piece (zeros from the
  file's offset 0). No tagged block of another file, no other bytes.
* **55 cut later writes**: 48 clean prefixes, 7 zeroed; none with
  another file's bytes.
* **The geometry of 035-01**: the wrong bytes begin at a multiple of 64
  pages (1 MiB) from the write's first page, or at its second page, and
  the length is a multiple of 16 KiB in the same piece.
* **The wrong pages are the file's blocks**: in all 93 cut files
  measured (forced, then `st_blocks`), the allocated bytes covered the
  length: the wrong pages are not a hole.
* **Rates**: 63 of 27,998 first writes that a kill found were cut (1
  in 444) in the runs with a prepared file and a pause, and in the
  rotations, from 11:58, at load averages of 10 to 27 (`uptime`); none
  of 11,924 in the runs started from 12:49 on, at 6 to 11
  (`week.sh`'s conformance steps had ended), which each differed in a
  way: no pause, no prepared file, or the parent's deletes forced.
  Which of these, or the load, stopped the cuts is not known.
* The device helper found, in 15 of 25 cut files, blocks of the wrong
  range among those of files of earlier trials; whether those files'
  bytes had reached the device is not known (their writes were cut, or
  not yet forced), which the next section settles another way.

### 6.2. A write whose copy fails, without a kill

035-01's hypothesis (section 9 there) is that a kill makes the kernel's
copy of the write fail. A write can be made to fail so without a kill:
from memory whose pages end inside the write (section 4.2). On APFS,
in every try, this reproduces what the kills left:

* **`EfaultProbe`** (Java, 60 tries on the internal SSD): every write
  threw `IOException` ("Bad address", EFAULT), yet the file's length
  was the cutoff, and its bytes were right only up to the last 1 MiB
  boundary before it; from there to the length, zeros.
* **`efault2`** (the same in C, with the device's blocks; 420 tries,
  2026-11-26, 13:02 to 13:08): 416 with wrong bytes, all from a 1 MiB
  boundary, all zeros; in 177 of them the wrong range lay, in part or
  in whole, in device blocks that a deleted file had held with its
  written and forced bytes (0x5a, or an earlier try's own value),
  deleted up to about a minute before. No byte of a deleted file came
  back.

So on F53's internal SSD the blocks of a deleted file, given to a new
file and not written by it, read as zeros: measured for the blocks that
deleted files had held seconds to a minute before.

### 6.3. Block reuse and preallocation

Small helpers outside the probes (2026-11-26, kept with the run data):

* **Reuse**: a file of 8 MiB written and forced, deleted, then 50 ms
  later a new one of 8 MiB, eight times: the new file had exactly the
  deleted file's blocks twice, and blocks of a file deleted earlier in
  the others. APFS gives new files the blocks of deleted ones, at the
  same offsets too.
* **Preallocation**: after a file of 8 MiB of 0x5a was deleted, a new
  file made with `F_PREALLOCATE` and `ftruncate` to 8 MiB, forced, read
  as zeros, on the internal SSD and on the RAM disk, also where its
  blocks were exactly the deleted file's (the RAM disk, 5 of 6). APFS
  reads a range that a file never wrote as zeros; the dropped pages of a
  failed copy are not such a range for it (section 7).


## 7. F53: an APFS RAM disk and an APFS disk image

### 7.1. The RAM disk

Runs of 2026-11-26, 12:03 to 12:47, one at a time; `rD-any-F` in four
runs (an earlier version of the probe in the first).

| run             | sizes       | trials | first W | first cut | stale | later W | later cut |
|---|---|---:|---:|---:|---:|---:|---:|
| rA-first0-F     | 64 KiB–8 MiB |  2,399 | 1,882 | 0 | 0 |  11 | 0 |
| rB-first1-N-lag | 64 KiB–8 MiB |  1,500 |   388 | 0 | 0 | 430 | 0 |
| rC-later-F      | 64 KiB–8 MiB |  1,000 |    17 | 1 | 0 | 346 | 0 |
| rD-any-F        | 2–8 MiB      |  3,917 |   613 | 3 | 3 | 723 | 0 |
| rE-first3-F     | 2–8 MiB      |  3,227 |   936 | 3 | 3 | 373 | 1 |

"first W" and "later W": the kills that found a first write of a file,
or a later write; "cut": those that left a prefix or wrong bytes;
"stale": a deleted file's bytes among them.

* **A deleted file's bytes in 6 of 7 cut first writes**: every first
  write cut in a later piece (from page 128, 256 or 384: 2, 4 or 6 MiB)
  held, from the start of that piece to the length, blocks of a file
  that the same child had deleted; the seventh was cut in its first
  piece and read as zeros, as in 035-01. The one later write cut left a
  clean prefix.
* **Whose, and where**: the tags name files of the same child, deleted
  one to five files before (when the next file was opened, 035-01's
  order), and their offsets: the same offsets (delta 0) in 2 cases,
  2,248,704 to 13,058,048 bytes further (a multiple of 4 KiB) in 4; one
  run held blocks of two deleted files and 9 blocks of freed APFS
  metadata (B-tree nodes by their object headers), whose bytes the
  probe does not keep.
* **The blocks are the file's**: all 7 cut files had blocks for their
  whole length. In the 4 measured with the device helper, the wrong
  range lay also in blocks that files of the 1 to 5 trials before had
  held: the RAM disk's few free blocks are given again and again.
* **When**: only kills that found the first write of a file in a child
  that had written files before (`rD`, `rE`: files 1 to 6); the first
  write of file 0 in a fresh child (`rA`) was never cut in 1,882 kills
  that found it.

### 7.2. The disk image

Runs of 2026-11-26, 12:47 to 13:01, one at a time, with fsync (S), as
an F_FULLFSYNC on a disk image is slow (035-01, section 7).

| run         | sizes        | trials | first W | first cut | stale | later W | later cut |
|---|---|---:|---:|---:|---:|---:|---:|
| gE-first3-S | 2–8 MiB      |  1,500 | 682 | 0 | 0 |  1 | 0 |
| gD-any-S    | 2–8 MiB      |  1,000 | 164 | 4 | 4 | 58 | 0 |
| gA-first0-S | 64 KiB–8 MiB |  1,000 | 853 | 0 | 0 |  0 | 0 |

* **4 of 4 cut first writes held a deleted file's bytes**, all of
  035-01's random kill (`gD`), each from a later piece to the length.

### 7.3. A write whose copy fails, on the RAM disk and the image

`efault2` as in section 6.2, 2026-11-26, 13:04 to 13:06:

* **RAM disk**, 60 tries: all with wrong bytes, from a 2 MiB boundary;
  in 52 the wrong range lay in blocks that a deleted file had held, and
  50 showed another file's bytes (the deleted files' 0x5a in 40, an
  earlier try's value in 17): 39.8 MB of 0x5a, 12.6 MB of other bytes,
  17.0 MB of zeros. The 10 cut in their first piece read as zeros.
* **Disk image**, 40 tries: all with wrong bytes, from a 2 MiB boundary;
  34 showed another file's bytes (16.7 MB of 0x5a, 18.5 MB of other
  bytes, among them the earlier runs' tagged blocks); the 6 cut in their
  first piece read as zeros.

Where a deleted file's blocks still hold its bytes, a failed copy shows
them: the internal SSD's zeros come from the device, or from APFS on
it, not from the way the write fails.


## 8. s1: Linux, ext4

Runs of 2026-11-26, 11:59 to 12:59, one at a time.

| run             | sizes        | trials | first W | first cut | later W | later cut | wrong bytes |
|---|---|---:|---:|---:|---:|---:|---:|
| sA-first0-F     | 64 KiB–8 MiB |  3,000 | 2,876 | 494 |     0 |     0 | 0 |
| sC-later-F      | 64 KiB–8 MiB |  3,000 |    50 |  32 | 1,913 | 1,048 | 0 |
| sB-first1-F-lag | 64 KiB–8 MiB |  3,000 | 2,403 | 796 |     0 |     0 | 0 |
| sA-first0-N     | 64 KiB–8 MiB |  2,000 | 1,933 | 318 |    22 |     5 | 0 |

* **Only prefixes**: 11,000 kills, 2,693 cut writes, each a clean
  prefix; no zeros, no other file's bytes, as in 035-01, section 8.
* **`EfaultProbe`** on s1 (100 tries, page 4,096): every write
  returned short, the bytes before the cutoff, and the file held exactly
  those: no wrong byte. Where APFS fails the write and keeps the length,
  Linux returns what it copied.


## 9. What the measurements say

* **Measured**: on APFS a write whose copy fails, by a kill or by
  EFAULT, keeps the file's length where the copy got, and the pages of
  the failed piece are blocks of the file that were never written
  (sections 6 and 7). On the RAM disk and the disk image those blocks
  hold what a deleted file left in them, on F53's internal SSD zeros,
  also where the blocks had held a deleted file's forced bytes seconds
  to a minute before (section 6.2). Cut in its first piece, a first
  write read as zeros on every device.
* **Measured**: APFS gives new files the blocks of deleted files, at
  the same offsets or others (sections 6.3 and 7.1); a stream file of
  BergDB at the same offsets as an older one has its meta blocks at the
  same places (section 10).
* **Hypothesis, not tested**: APFS on the internal SSD unmaps (TRIM) a
  deleted file's blocks, and the SSD reads unmapped blocks as zeros; a
  RAM disk and a disk image (whose blocks are bytes of a file) keep
  them, and so would, by the same reasoning, an external disk without
  TRIM. A block given again before its unmap would show the old bytes
  on the internal SSD too; the delays measured (seconds to a minute
  between a delete and the reuse) did not.
* **Not known**: why the kills cut a write so rarely (1 in 444 first
  writes found, with a prepared file forced shortly before; none in
  11,924 later, section 6.1); 035-01's later writes in older processes
  were cut more often.


## 10. For BergDB: what a start does with another file's bytes

Read in the code of main at `2a6ff06c` (2026-11-26), and tried with a
throwaway test outside `java/` (section 10.3).

### 10.1. Nothing ties a meta block or a record to its place

* **Stream files and meta blocks.** Every file size of `FileStream` is a
  multiple of 200,000 bytes (`SMALLEST_FILE_SIZE`), the meta block
  distance, and a file's name is its first position over 100,000; so
  every stream file begins at a multiple of 200,000, and a meta block
  lies at the same offsets in every file: 0, 200,000, 400,000 and so on.
  A deleted file's blocks given to a new file at the same offsets, as
  APFS gives them (sections 6.3 and 7.1), put the deleted file's meta
  blocks exactly at the new file's meta positions.
* **A meta block** (`MetaBlock`, 128 bytes) holds the magic bytes
  "berg", the version 155, the creation's time, the position of the
  last record completed before the block, the database's ID (16 random
  bytes), the maximum node size and the last byte 10; not its own
  position. The time, the ID and the node size are the same in every
  block of a database, and the start does not compare the ID with
  anything: a block of an older file of the same database differs from
  one of the last file only in the record it names.
* **A record** (`StoredTrans`): its size, the format byte 8, three
  unused bytes, the transaction's time, its startup position and its top
  node's position, the nodes, each with a CRC-32C of the node's bytes
  (`NodeChecksum`), not of its position, and the last byte 10. Its
  pointers name earlier positions; nothing names its own. A record read
  at another position than where it was written keeps valid checksums
  when the meta positions inside it lie at the same places, as they do
  at the same offset in another stream file (delta 0); at another delta
  the 128 bytes that the reader skips are other bytes, and a checksum
  fails as a rule.

So neither a meta block nor a record is refused because it was written
at another position or in another file; what refuses them is what they
name, and their checksums when they are read at another delta.

### 10.2. The start's reads, in order

`Db.startInner()`:

1. `refuseOtherNodeSize()`, then `recover()`, both through
   `readLastValidMetaBlock()`: the meta positions from the last one
   wholly within the stream's length backwards. A block of 128 zero
   bytes is not valid and is passed over (028-60, part 1); a valid one
   (the magic bytes, the version, the last byte 10) is taken; any other
   bytes throw `BadMagicBytes`, and the start refuses with "Invalid
   magic bytes in stream: the stream is not a BergDB stream, or it is
   damaged; or an earlier release of BergDB, 2026.3 or before,
   encrypted it ...". Nothing is written.
2. `checkLastTransSpos()`: a block that names a record before the
   stream's first position, or not before the block, is refused: "The
   meta block at P names the last transaction at S, which cannot be one
   in a stream from F: not before the block." Nothing is written.
3. `fixLastTransactionIfNeeded()`: the walk from the named record by
   the records' sizes alone. A size below 5 or negative is refused, "Bad
   transaction size in db stream, S, spos P"; a size that reaches past
   the stream's end completes that record with zeros, as an aborted
   one: up to 2^31 − 1 bytes appended (`appendZeros`). The last byte and
   the format are not read.
4. `readStartupPos()`: the records from the named one to the end, each
   committed one parsed (its last byte 0 or 10, its format byte, every
   node's checksum, the content's length; `checkStartupPos()`); the last
   one's startup position; then `readTransactions()` from there and
   `DbStarter`.

What a start does with an older file's bytes from a page boundary Z to
the length L of the last file:

* **Inside the last record** (its size before Z, its end past L): as
  for zeros, the record is completed with zeros and aborted, and the
  start takes the records before it; the older bytes are not read.
* **Over a meta position**, at delta 0: the older file's meta block is
  there, valid, and taken as the last valid one (step 1). Of the same
  database, it names a record of the deleted file, before the stream's
  first position: refused at step 2, nothing written. Of another
  database whose positions lie in the same range, it passes step 2, and
  the walk (step 3) begins at a position of the last file that is not a
  record's start: refused there, or after a zero fill. At other deltas
  other bytes lie at the meta position: refused at step 1 ("Invalid
  magic bytes"). A run of more than 200,000 bytes always covers a meta
  position; the runs measured on APFS reach 62 pages (1 MiB) on the
  internal SSD and 4 MiB on the disk image (035-01, section 10).
* **Otherwise** the walk reaches the end of a record of the last file
  inside the run and reads the next size from the older bytes, as a
  rule from the middle of an older record: any 4 bytes. Negative or
  below 5: refused at step 3. Past the end: zeros are appended up to
  that size, up to 2 GB; then step 4 reads the record before, whose
  last byte lies among the older bytes, and refuses it ("Bad lastByte")
  unless that byte is 0 or 10. Inside the run: the walk goes on through
  the older bytes, and ends in one of these.
* **On a record of the older file**: where a record of the last file
  ends exactly where one of the older file began, the walk goes on
  through the older records, and step 4 parses them. In the test they
  were refused by a checksum (at another delta, or a pointer to a
  position that holds other bytes), or the walk ended as above. Records
  of the database's own deleted file name positions before the
  stream's first position (their startup position, their pointers),
  which a start cannot read (by the code, not made in the test).

### 10.3. The throwaway test

A program in the package `bergdb.core`, on the branch's build, kept
outside the repository with the run data: a database (the Core's
`Db`, `FileStream` without forcing) of 1,500 keys, values of 50 to
4,050 random bytes, a startup distance of 300,000 bytes and a retain
duration of 1 s, written until reclaim's cuts had deleted 20 files of
1 MB, each copied before its deletion; a second database of another
seed in the same way. On copies, the first database's last file
(834,280 bytes, from 63,000,000) was given an older file's bytes from Z
to L (Z every 16 KiB, L 1, 8 or 62 pages after Z) and started; each
start's state was compared with every prefix of the transactions.
Appends past 20 MB were kept in memory, not written (a zero fill of up
to 2 GB is seen, not made). Outcomes:

* **Inside the last record** (an earlier version: files of 200 kB, a
  last record of 700 kB): 48 starts, all with the last transaction
  lost and every other.
* **The database's own deleted file, delta 0**: over a meta position,
  168 of 168 refused at step 2, nothing written; elsewhere 132: 77
  refused at step 3 (a size), 48 refused at step 4 after a zero fill
  (a bad last byte), 7 started with a prefix of the transactions (one
  after a fill of 29 MB).
* **Another database's deleted file of older positions, delta 0**: over
  a meta position 168 of 168 refused at step 2; elsewhere 132: 62
  refused (a size), 2 (a last byte), 62 fills that the test then stopped
  at 20 MB (an earlier version), 6 started with a prefix.
* **Another database's file of the same positions, delta 0**: over a
  meta position 168: 84 refused at step 3 (a size), 84 after a zero fill
  ("Transaction at start pos N is not committed"); elsewhere 132: 59
  refused (a size), 53 after a zero fill (a last byte), 3 by a
  checksum, 17 started with a prefix, 8 of them after fills of 58 MB to
  994 MB.
* **On a record of a deleted file**: where a record of the last file
  ends where one of a deleted file began: at delta 0, 3 cases, all of
  the other database (1 refused by a checksum, 2 fills stopped by the
  test); at deltas of a multiple of 4 KiB, 337 cases: 269 refused by a
  checksum, 47 by the magic bytes, 13 by a size, 8 fills stopped by the
  test.

No start took another file's records as its own: each of the 78 that
started had the state of a prefix of the transactions. Wrong data (S1)
needs records of another file that pass every check at their new place
and name records that parse; the database's own deleted files name
positions before the first position, and another database's records
name positions that hold other bytes. Neither rules it out: nothing in
a record says where it belongs.


## 11. For BergDB: the options, a draft for a 028 entry

A draft for the lead to register as a 028 entry (Kind: Fix; Frans:
decision), beside 028-60's part 2.

**What.** After a kill of the process during an append on APFS, the
last stream file can hold, from a page boundary to its length, the
bytes of a file deleted before, not zeros: on an APFS RAM disk and an
APFS disk image, in the first write of a new file, from its second
piece on (035-01, section 7; 035-02, section 7). Not seen on F53's
internal SSD in 63 cut first writes of a new file and 476 failed
copies, where the blocks of deleted files read as zeros (section 6).
In BergDB the deleted file is an older stream file, deleted by a cut of
reclaim, or another database's file on the same volume; as every
stream file begins at a multiple of 200,000, an older file's meta
blocks can lie exactly at the last file's meta positions.

**Why.** Today a start refuses such a tail in most cases, with a
message that names neither the cause nor the way out: "Invalid magic
bytes in stream: the stream is not a BergDB stream ...", "The meta
block at P names the last transaction at S, which cannot be one ...",
"Bad transaction size", "Bad lastByte", "is not committed", a checksum
(section 10). Some of these refusals come after the start has appended
zeros for a size read from the older bytes, up to 2 GB; some starts
succeed after such a fill, with the right data and a stream larger by
up to 2 GB. No start took another file's records as its own in the
constructed cases, but nothing in a record or a meta block rules it out
(section 10.1). A database that does not start after a kill is S2
(033's rules), data from another file would be S1. 028-60's options B1
to B3 are about zeros; under B2 these tails are refused as under B1, or
before the walk.

The options:

* **C1. Refuse with the cause and the way out, before writing.** At the
  start, in the last file: a meta block that names a record before the
  stream's first position, or of another database (its ID not that of
  the block before it), is not valid, as a block of zeros is not; other
  bytes than a block or zeros at a meta position, a size that cannot be
  one, a bad last byte or a checksum in the records after the last
  valid block mark the start of a tail that is not the stream's own,
  at P, the end of the last record that is right. The start then
  refuses with one message: from P the last file holds bytes that are
  not this stream's, as a kill during an append on macOS (APFS) can
  leave them (035-02); keep a copy, cut the file at P less its first
  position, and start. B1's message for zeros, with the same cut. And
  the recovery completes a torn last record with zeros only after the
  Core has found its header to be one (the format byte, a time not
  before the record before it, a startup position before it), so that a
  size from other bytes no longer makes the start append up to 2 GB
  before it refuses. Cost: about 80 lines and tests, no format change;
  the header check crosses the layers (recovery parses no record today,
  `RecoverableStream.MIN_TRANS_SIZE`'s Javadoc), so a hook from the
  Core. Risk to data: none. A person still cuts the file (S2 stays).
* **C2. Cut such a tail, as B2 cuts zeros.** With C1's checks and B2's
  conditions (P in the last file; the run from the page boundary at or
  before P to the end at most 8 MB; the length a multiple of 4,096),
  the start cuts the stream at P and goes on. Cost: B2's new storage
  operation, a cut of the tail at recovery, and C1's checks. Risk: as
  B2's, a tail that a storage damaged is cut without a word; and a
  record of another file that passes every check (S1) is taken, as
  today.
* **C3. Tie meta blocks and records to their place.** A meta block
  holds its own position (in the reserved bytes from offset 46); a
  record holds a check of its position and the database's ID (each
  node's CRC-32C begun with the node's position and the ID, or a check
  of the header in its three unused bytes). A block or a record of
  another file, or of another place, is then not valid, as a block of
  zeros is not, and C1's checks and C2's cut are exact. Cost: a change
  of the stream format (the meta block's version and the record
  format, 027-03), for new databases; a few bytes, no measurable time.
  Risk: low. It fits the stream format work that the release themes
  postpone (a stable format with encryption and replication).
* **C4. Keep older bytes out of new files.** `FileStream` writes a new
  file's whole size in zeros and forces it before the file takes
  appends, so that a dropped piece reads the file's own zeros (and B2
  covers it); or the cut's thread zeroes a file's meta positions before
  it deletes the file. The first doubles what is written and changes
  `FileStream`'s length, which is its last file's length today; the
  second removes only the meta blocks, and costs a forced write per
  meta position. Not recommended.

Recommendation: C1 for the next release, with 028-60's part 2 (B1 or
B2 as Frans decides; with B2, C2 is a small step after C1), and C3 with
the next change of the stream format, after which C2's cut is exact.
Reasons: the tails seen with another file's bytes are on devices other
than F53's internal SSD; a start refuses them today, with the wrong
words, and its zero fill of up to 2 GB is a cost of its own; C1 gives
the right words and stops the fill now, C3 removes the doubt that
nothing ties bytes to their place.

Done when (C1): the checks and the message; unit tests on a file
stream with zeros, an older stream file's bytes at the same offsets and
at others, another database's blocks, and a size from other bytes, each
refused with the message and nothing written, and each file cut at P
then starting; `java/before-commit.sh`; 027-11's start steps and
`Database`'s Javadoc ("What a crash keeps").


## 12. State

2026-11-26, by an agent of lead-1126.

* **Done:** section 3's parts 1 to 5: the probes (section 4), the
  environments (5), F53's internal SSD (6), the RAM disk and the disk
  image (7), s1 (8), what the measurements say (9), what a start of
  BergDB does with another file's bytes, by the code and a throwaway
  test (10), and the options as a draft for a 028 entry, with a
  recommendation (11).
* **Kept:** outside the repository, each run's TSV file and summary,
  the files kept with another file's bytes (RAM disk, image) with the
  end of their logs, the helpers for reuse and preallocation, and the
  throwaway test's source and outputs; the lead can ask for them. The
  RAM disks and the disk image were detached and the image deleted;
  nothing of the probes is left on s1.
* **Not settled:** why the kills cut writes so rarely, and why the rate
  fell during the day (section 6.1); the TRIM hypothesis (section 9);
  external disks with APFS, which were not at hand; wrong data from
  another database's deleted file whose records parse at their new
  place, which the test did not make (section 10.3).
* **Next:** the lead registers section 11 as a 028 entry, beside
  028-60's part 2, for Frans's decision.


## Log

2026-11-26. Created (Frans), in 035.

2026-11-26. Done by an agent of lead-1126, in the clone c352 (branch
`035-02`): `StaleBytesProbe`, `EfaultProbe` and two helpers. On F53's
internal SSD 59,930 kills, 39,952 of them during the first write of a
new file, 63 of those cut: all zeros or prefixes, no deleted file's
bytes; 476 writes that failed inside their copy without a kill (EFAULT)
left the same geometry, all zeros, 177 of them in blocks that a deleted
file's forced bytes had held. On an APFS RAM disk and an APFS disk
image 6 of 7 and 4 of 4 cut first writes, and 84 of 100 failed copies,
showed a deleted file's bytes. s1 (ext4): prefixes only, and short
writes. For BergDB: nothing ties a meta block or a record to its place;
a start refuses such a tail in most cases, with messages that name
neither the cause nor the way out, at times after a zero fill of up to
2 GB; no start took another file's records in about 1,300 constructed
cases. Options C1 to C4 as a draft for a 028 entry; recommended: C1
now, C3 with the next change of the stream format (section 11).
