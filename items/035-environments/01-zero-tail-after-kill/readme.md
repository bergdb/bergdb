# 035-01. Zeros within a file's length after a kill

Created 2026-11-26 by Frans Lundberg. Status: open.

Why a kill of a process that appends to a file can leave zeros within
the file's length on macOS (APFS), how often, and whether other systems
do it; for 028-60's part 2 (what BergDB's start does with a tail of
zeros, options B1 to B3), which waits for this item's first results.


## 1. What is known

* 031-02, F1: three times in about 9,500 kills (SIGKILL, F53, macOS,
  APFS) of KillWriter's child, the last stream file read as zeros from
  a page boundary to its end: 458,752 bytes (28 pages of 16 KiB) from
  offset 3,915,776 of a file of 4,374,528 (seed 63); 114,688 bytes (7
  pages) from 14,778,368 of a file of 14,893,056 (seed 91). Every
  transaction that a sync had returned for was intact; the zeros were
  in the write that the kill interrupted, before its force.
* `ZeroTailProbe` (031-02, `apps/`), without BergDB: a Java process
  appends chunks of 64 kB to 2 MB with `RandomAccessFile.write()` and
  forces each; killed at random after 0.3 to 0.9 s, 1 in 150 files
  ended in 442,368 zero bytes (27 pages) within the file's length.
* Both files of the kills are a whole number of 16 KiB pages long, as
  are the starts of their zeros, though BergDB's records have any size;
  in seed 91 the record that the zeros reach is longer than the file
  (028-60, section 1).


## 2. The hypothesis

As written on 2026-11-26, before the study; section 9 holds what the
measurements show instead. The kernel (XNU) copies a large write into
the page cache in chunks of pages, and moves the file's end to a chunk's end, a page
boundary, before it copies the chunk's pages; a SIGKILL stops the write
between pages and does not move the end back; the pages not copied read
as zeros. The file is then a prefix of the write and zero pages up to a
page boundary. On Linux the size is believed to grow page by page as
data are copied, so a kill leaves a shorter file without zeros: the
prefix that 014-01, section 7, assumes.


## 3. The study

1. `ZeroTailProbe` extended: each write's intended end and size
   recorded before the call, so that every zeroed file is compared with
   the write it cut: is its length a whole number of pages, and short
   of the write's end? Where do the zeros start, in pages from the
   write's start?
2. Writes of one page or less, of exactly a chunk, and of many sizes up
   to 8 MB: which sizes give zeros, and the size of the runs.
3. With and without a force after each write; a write by
   `FileChannel` and by `RandomAccessFile`; kills at random times.
4. Another file system on F53 if one is at hand (an HFS+ disk image, a
   RAM disk).
5. The same probe on s1 (Linux): zeros or not.
6. What it means for 028-60's part 2: whether B2's conditions can add
   that the zeros start at a page boundary and the file ends at one,
   and whether other systems need the cut at all.


## 4. The probe

[probes/ZeroTailProbe.java](probes/ZeroTailProbe.java), 031-02's
`ZeroTailProbe` extended (2026-11-26); its header gives the options.

* **The child** appends writes to a file, each filled with one byte
  value that is never 0 and differs from the write before (1 + seq %
  255). Before each write it appends the line `W seq start size` to a
  side log, after the write returns `w seq`, after the force `f seq`.
  Each line is one `write()` call that returns before the next step
  begins, so after the kill the log names the write that the kill
  found, if any; its intended start S, size N and end E = S + N. At a
  cap (32 MiB by default) the child opens the next file and deletes
  the last.
* **The parent** starts the child, waits for its line `ready` (the file
  is open), sleeps 20 to 400 ms and kills it with
  `Process.destroyForcibly()` (SIGKILL). It then reads the last file
  and compares each write's bytes within the file's length L with its
  fill byte. One line per trial in a TSV file.
* **Classes of a trial**: complete (L = E), none (L = S), prefix (S < L
  < E, every byte right), zeros (a byte 0 within L, from Z on), and
  short, long or garbage (another wrong byte) for anything else. Short
  and long were never seen; garbage only as section 7's old bytes.
* **The kills that found a write** are those whose log ends in `W`: the
  kill came after that line, before the next. Such a kill finds the
  write before it begins, during it, or after it returned and before
  its `w`; the others found the force (`w`) or the start of the next
  write (`f`). With F_FULLFSYNC after each write about one kill in ten
  found a write, with fsync one in three, without a force seven in
  ten.
* **Pages from the write's first page**: the measured positions are
  given as (X − ⌊S / p⌋·p) / p, with p the page size, 16 KiB on F53:
  the position X in pages from the start of the page that holds the
  write's first byte.
* Run as `java ZeroTailProbe.java parent DIR TRIALS key=value...`; for
  example, 031-02's case is `api=raf force=1 size=r:65536:2065535`, the
  default. The runs of sections 6 to 8 set `label` to the run's name
  and the options its row gives: F, S and - are `force=1`, `2` and `0`;
  a size range is `size=r:MIN:MAX`, one size `size=f:N`; files of 64
  MiB are `cap=67108864` (the default is 32 MiB), `cap8` and `cap16`
  are 8 and 16 MiB; the runs named `c-` and `-s2` have `seed=2`. The
  delay is the default, 20 to 400 ms.


## 5. The environments

* **F53**: MacBook Pro (MacBookPro18,3), Apple M1 Pro, 32 GB; macOS
  27.0.1 (26A434), Darwin 27.0.0, `xnu-13432.1.9~1/RELEASE_ARM64_T6000`;
  page size 16,384 (`hw.pagesize`); the data volume APFS on the
  internal SSD (`disk3s1`, "Apple Fabric", solid state); OpenJDK
  27.0.1.1 (Homebrew). Beside the probes, `java/week.sh` and other
  sessions' work ran: load averages 10 to 17 (`uptime`) during the
  runs. Other file systems, made for the probe with `hdiutil` and
  removed after: HFS+ and APFS on sparse disk images of 2 GB on the
  internal SSD, and HFS+ and APFS on RAM disks of 512 MiB
  (`ram://`).
* **s1, a Linux VPS**: Ubuntu 26.04 LTS, kernel 7.0.0-30-generic,
  x86_64, KVM (QEMU) with 2 virtual CPUs (AMD EPYC-Rome), 3.8 GB;
  page size 4,096 (`getconf PAGESIZE`); ext4 (block size 4,096,
  `rw,relatime,discard,commit=30`) on a virtual disk of 50 GB ("QEMU
  HARDDISK", not rotational); Temurin JDK 27.0.1.1+4, unpacked for the
  probe and removed after. Nothing else ran (load average below 0.2
  before the runs); the probes ran with `nice -n 10`.


## 6. F53: APFS on the internal SSD

Runs of 2026-11-26, 10:29 to 11:31, two to four at a time. Sizes:
`r:65536:2065535` is written 64 KiB–2 MB (031-02's), `r:2097152:8388608`
2–8 MiB. Force: F is `FileChannel.force(true)` (F_FULLFSYNC, as
FileStream's hard sync), S `FileDescriptor.sync()` (fsync), - none.
API: raf `RandomAccessFile.write` (as FileStream), fc `FileChannel.write`
of a heap buffer, fcd of a direct buffer. Files of 32 MiB, 64 MiB for
writes over 2 MB, 8 or 16 MiB where the name ends in `cap8` or
`cap16`. "Found a write": kills whose log ends in `W` (section 4), and
how those files ended.

| run | sizes | force | API | trials | found a write | complete | none | prefix | zeros |
|---|---|---|---|---:|---:|---:|---:|---:|---:|
| s-16k-force       | 16,384            | F | raf |   600 |  20 |  13 |   7 |   0 | 0 |
| s-4000-force      | 4,000             | F | raf |   600 |  23 |  12 |  11 |   0 | 0 |
| c-16k-noforce     | 16,384            | - | raf |   800 | 562 | 353 | 209 |   0 | 0 |
| c-4000-noforce    | 4,000             | - | raf |   800 | 592 | 347 | 245 |   0 | 0 |
| s-1m-force        | 1,048,576         | F | raf |   600 |  48 |  35 |  13 |   0 | 0 |
| s-1000000-force   | 1,000,000         | F | raf |   600 |  68 |  43 |  25 |   0 | 0 |
| c-1000000-force   | 1,000,000         | F | raf | 1,200 |  86 |  61 |  25 |   0 | 0 |
| a-raf-force       | 64 KiB–2 MB       | F | raf | 1,500 | 166 | 115 |  49 |   0 | 2 |
| a-fc-force        | 64 KiB–2 MB       | F | fc  |   800 | 130 |  80 |  50 |   0 | 0 |
| a-fcd-force       | 64 KiB–2 MB       | F | fcd |   800 |  92 |  65 |  26 |   0 | 1 |
| d-raf-fsync       | 64 KiB–2 MB       | S | raf | 1,000 | 312 | 226 |  85 |   0 | 1 |
| b-raf-noforce     | 64 KiB–2 MB       | - | raf | 1,500 | 980 | 706 | 254 |  20 | 0 |
| b-fc-noforce      | 64 KiB–2 MB       | - | fc  |   600 | 413 | 293 | 109 |   9 | 2 |
| b-fcd-noforce     | 64 KiB–2 MB       | - | fcd |   600 | 345 | 263 |  66 |  16 | 0 |
| s-2m8m-force      | 2–8 MiB           | F | raf |   600 | 135 |  79 |  47 |   2 | 7 |
| c-2m8m-force-s2   | 2–8 MiB, seed 2   | F | raf | 1,500 | 200 | 125 |  69 |   0 | 6 |
| e-2m8m-force-cap8 | 2–8 MiB           | F | raf | 1,500 | 149 |  89 |  60 |   0 | 0 |
| d-2m8m-fsync      | 2–8 MiB           | S | raf |   800 | 265 | 198 |  65 |   2 | 0 |
| e-2m8m-fsync-cap8 | 2–8 MiB           | S | raf | 1,000 | 284 | 217 |  67 |   0 | 0 |
| b-2m8m-noforce    | 2–8 MiB           | - | raf |   800 | 598 | 352 | 132 | 108 | 6 |
| s-8m-force        | 8,388,608         | F | raf |   600 | 131 |  77 |  48 |   1 | 5 |
| f-8m-force-cap16  | 8,388,608         | F | raf | 1,200 | 131 | 101 |  29 |   0 | 1 |
| f-8m-fsync-cap16  | 8,388,608         | S | raf | 1,200 | 386 | 297 |  85 |   0 | 4 |

In all: 21,200 trials, 6,116 kills that found a write, 158 prefixes
and 35 zeroed files. No trial ended short, long or with a wrong byte
other than 0. In every trial the writes before the last one were
intact.

### 6.1. The zeroed files

35 files, each compared with the write that the kill cut (S, N, E):

* **Lengths:** every length L is a multiple of 16,384, the page size,
  and shorter than the write's end: L < E in all 35.
* **Zeros:** from Z to the file's end, Z a multiple of 16,384 in all 35;
  every byte before Z is right, and the first wrong byte is always in
  the last write: no earlier, forced write lost a byte.
* **Where Z is**, in pages from the write's first page: at 64·k pages,
  k from 1 to 7, in 27 files; at page 1 in 6 files, the write's
  second page, where the write began inside a page and the bytes of
  its first page are right; at page 0 in 2 files, writes that began
  on a page boundary (8 MiB at 8 and 16 MiB). So Z is the start of a
  piece of 64 pages (1 MiB) of the write, counted from its first page,
  or the first whole page of the write's first piece.
* **Where L is**: in the same piece as Z, 1 to 62 pages after it (all
  35 under 64): 1, 6, 6, 7, 10, 11, 12, 12, 12, 14, 16, 16, 16, 17, 20,
  21, 26, 26, 27, 28, 28, 29, 31, 38, 39, 40, 42, 44, 47, 50, 51, 53,
  53, 54, 62. Never at the piece's end, nor at the write's end.
* 031-02's runs of 27 and 28 pages appear again (s-8m-force), and of 7
  pages (b-2m8m-noforce), as in 028-60's seed 91.

### 6.2. The prefixes

158 kills left a clean prefix of the cut write, without zeros: in all
158, L is at 64·k pages from the write's first page (k from 1 to 6),
the end of a piece. 153 of them without a force; with a force 5.

### 6.3. Which writes are cut, and how

* **One page or less** (16,384 and 4,000 bytes): 1,197 kills found
  such a write, with or without force; none was cut (the file held
  all of it or none of it).
* **One piece, on a piece boundary** (1 MiB at multiples of 1 MiB): 48
  kills found such a write; none was cut. **1,000,000 bytes**, at most
  two pieces: 154, none cut.
* **64 KiB–2 MB**: with a force (F or S), 4 zeroed files in 700 kills
  that found a write; without, 2 zeroed and 45 prefixes in 1,738.
* **2–8 MiB and 8 MiB**, in files of 64 MiB: with F, 18 zeroed and 3
  prefixes in 466; with S, 0 and 2 in 265; without force, 6 and 108 in
  598. 8 MiB in files of 16 MiB: with F, 1 zeroed in 131; with S, 4 in
  386.
* **Small files** (cap8: 2–8 MiB writes in files of 8 MiB): no write
  cut in 433 kills that found one, with F or S. Not explained.
* **Force**: with F_FULLFSYNC a cut write was zeroed 22 times and left
  a prefix 3 times; with fsync zeroed 5 times, a prefix twice; without
  force, zeroed 8 times and a prefix 153 times. A force is not needed
  for zeros, but makes them the usual outcome of a cut. FileStream
  forces by default.
* **API**: `RandomAccessFile` and `FileChannel` with a heap or direct
  buffer give zeros alike (2 of 166, 0 of 130, 1 of 92 with F): all
  three end in one `write(2)` of the whole buffer.
* **Rates**, for 031-02's sizes with F: 3 zeroed files in 388 kills
  that found a write, 3,100 kills in all. 031-02's 1 in 150 kills came
  with kills 0.3 to 0.9 s after the child's start, including the JVM's
  start; here 20 to 400 ms after the file was open, so the rates per
  kill differ by the time a kill finds a write.


## 7. F53: other file systems

| volume | run | sizes | force | trials | found a write | complete | none | prefix | zeros | old bytes |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| HFS+, RAM disk   | fs-raf-force      | 64 KiB–2 MB | F | 800 | 270 | 206 |  64 | 0 | 0 | 0 |
| HFS+, RAM disk   | fs-raf-noforce    | 64 KiB–2 MB | - | 400 | 247 | 200 |  47 | 0 | 0 | 0 |
| HFS+, image      | fs-raf-force      | 64 KiB–2 MB | F | 800 |  15 |  13 |   2 | 0 | 0 | 0 |
| HFS+, image      | fs-raf-noforce    | 64 KiB–2 MB | - | 400 | 106 |  98 |   8 | 0 | 0 | 0 |
| APFS, image      | fs-raf-force      | 64 KiB–2 MB | F | 800 |   6 |   5 |   1 | 0 | 0 | 0 |
| APFS, image      | fs-raf-noforce    | 64 KiB–2 MB | - | 400 |  88 |  36 |  52 | 0 | 0 | 0 |
| APFS, image      | fs-2m8m-force     | 2–8 MiB     | F | 400 |  10 |   6 |   4 | 0 | 0 | 0 |
| APFS, image      | fs-2m8m-fsync     | 2–8 MiB     | S | 600 | 108 |  38 |  69 | 0 | 1 | 0 |
| APFS, image      | e-2m8m-fsync-cap8 | 2–8 MiB     | S | 600 | 138 |  31 | 106 | 0 | 0 | 1 |
| APFS, RAM disk   | fs-raf-force      | 64 KiB–2 MB | F | 800 | 202 | 132 |  65 | 0 | 5 | 0 |
| APFS, RAM disk   | fs-raf-noforce    | 64 KiB–2 MB | - | 400 | 225 | 193 |  32 | 0 | 0 | 0 |
| APFS, RAM disk   | fs-2m8m-force     | 2–8 MiB     | F | 600 | 227 | 171 |  48 | 2 | 3 | 3 |
| APFS, RAM disk   | fs-2m8m-force-s2  | 2–8 MiB     | F | 800 | 293 | 226 |  61 | 1 | 2 | 3 |
| APFS, RAM disk   | e-2m8m-force-cap8 | 2–8 MiB     | F | 600 | 178 | 138 |  40 | 0 | 0 | 0 |

The HFS+ RAM disk's TSV files were lost: the disk was no longer
attached when they were to be copied; its counts are those its runs
printed. An F_FULLFSYNC on a disk image is slow, so few kills found a
write there with F.

* **HFS+**: no zeros and no prefix in 638 kills that found a write: a
  cut write left the file at the write's start (none) or whole.
* **APFS, other devices**: the same geometry as on the internal SSD,
  with another piece: 128 pages (2 MiB) on the RAM disk, 256 (4 MiB)
  on the image, by the prefixes (at 256 and 384 pages on the RAM disk)
  and the cut writes (below). In all 18 cut files the length and the
  start of the wrong bytes are multiples of 16,384, L < E, and L lies
  in the piece where the wrong bytes begin.
* **Old bytes, not zeros**: in 7 of the 18 cut files (6 on the RAM
  disk, 1 on the image) the pages from a piece's start to L held not
  zeros but the fill byte of an earlier write, of a file deleted before
  (for example, a child's file 9, its first write, seq 105, from 2 MiB
  on: the fill byte of seq 93, in the child's file 8, deleted). Each
  was the first write of a new file, cut in its second or third piece.
  Every write cut in its first piece read as zeros (11 files, 10 of
  them the first write of a new file). The internal SSD (APPLE SSD
  AP1024R, TRIM supported) gave only zeros, among them 3 first writes
  of a new file cut in a later piece (the third, fourth and sixth);
  whether a deleted file's bytes can appear there too is not settled.


## 8. s1: Linux, ext4

| run | sizes | force | API | trials | found a write | complete | none | prefix | zeros |
|---|---|---|---|---:|---:|---:|---:|---:|---:|
| a-raf-force       | 64 KiB–2 MB      | F | raf |   800 |  73 |   0 |  18 |  55 | 0 |
| a-raf-force-s2    | 64 KiB–2 MB      | F | raf | 1,200 | 116 |  11 |  28 |  77 | 0 |
| a-raf-noforce     | 64 KiB–2 MB      | - | raf |   800 | 599 |  49 | 101 | 449 | 0 |
| a-fc-noforce      | 64 KiB–2 MB      | - | fc  |   400 | 305 |  31 |  61 | 213 | 0 |
| a-fcd-noforce     | 64 KiB–2 MB      | - | fcd |   400 | 272 |  31 |   8 | 233 | 0 |
| s-4000-noforce    | 4,000            | - | raf |   400 | 277 | 186 |  62 |  29 | 0 |
| s-4096-noforce    | 4,096            | - | raf |   400 | 261 | 191 |  70 |   0 | 0 |
| s-1m-force        | 1,048,576        | F | raf |   400 |  31 |  23 |   8 |   0 | 0 |
| s-1m-noforce      | 1,048,576        | - | raf |   400 | 307 | 263 |  44 |   0 | 0 |
| s-1000000-noforce | 1,000,000        | - | raf |   400 | 286 |  20 |  36 | 230 | 0 |
| s-2m8m-force      | 2–8 MiB          | F | raf |   400 |  83 |   9 |  17 |  57 | 0 |
| s-2m8m-noforce    | 2–8 MiB          | - | raf |   400 | 308 |  24 |  86 | 198 | 0 |
| s-8m-force        | 8,388,608        | F | raf |   400 |  63 |  10 |  20 |  33 | 0 |

F is `FileChannel.force(true)`, fsync(2) on Linux.

* **No zeros**: 6,800 trials, 2,981 kills that found a write, 1,574
  prefixes, no zeros and no wrong byte.
* **A kill cuts a write where it is**: most kills that found a write
  left a prefix of it (with a force, 132 of 189 with 64 KiB–2 MB).
  Every prefix ends on a 4 KiB page boundary; 1,465 of 1,574 on a 64
  KiB boundary and 439 on a 2 MiB one (the 8 MiB writes at 512·k pages
  of 4 KiB): the page cache's folios. A write of 4,000
  bytes across a page boundary was cut at it (29 times); a write of
  one page (4,096 on a boundary) or of 1 MiB on a 1 MiB boundary was
  never cut.
* So on s1 the file after a kill is a prefix of what was appended:
  014-01, section 7's assumption holds there, and the start's recovery
  of a cut tail covers it.


## 9. The cause

Section 2's hypothesis, that the kernel moves the file's end to the
end of a chunk before it copies the chunk, does not fit: the length is
never at a piece's end, but 1 to 62 pages into it (section 6.1). What
fits every cut file, on all three APFS devices:

* **Measured**: a write is copied in pieces, aligned to the write's
  first page, of 64 pages (1 MiB) on the internal SSD, 2 MiB on the RAM
  disk, 4 MiB on the image. A kill during a write ends it in one of two
  ways: (a) a prefix up to the end of a piece, every byte right; (b) the
  pieces before the cut one right, then wrong bytes from the cut
  piece's first page that the write did not find in the cache (its
  start, or the write's second page) to L, a page boundary inside that
  piece. The wrong bytes read as zeros, or as a deleted file's bytes on
  a device that keeps them (section 7).
* **The published source** (xnu-12377.121.6, macOS 26; F53 runs
  xnu-13432, not published), `bsd/vfs/vfs_cluster.c`:
  `cluster_write_copy()` copies a write into the page cache in pieces
  of at most `cluster_max_io_size()`, the device's largest write and
  never less than `MAX_UPL_TRANSFER_BYTES`, 1 MiB; a piece ends at a
  multiple of that size from the write's first page. In each piece it
  copies first into pages already in the cache
  (`cluster_copy_ubc_data_internal`: the write's first page when it
  holds the end of the last write), then into a UPL of new pages, page
  by page (`cluster_copy_upl_data`, one `uiomove64` per page, which
  advances the write's offset). When a copy into the UPL fails, the
  whole UPL is aborted (`ubc_upl_abort_range(upl, 0, upl_size,
  UPL_ABORT_FREE_ON_EMPTY)`): its pages are dropped, with what was
  copied into them, while the write's offset stays past the pages
  copied.
* **The length**: APFS, whose source is not published, sets the
  length after the copy; the lengths measured are where the copy got
  (a page boundary inside the piece), so the pages of the aborted UPL
  are inside the length and read from the device: zeros where its
  blocks hold none (or were trimmed), old bytes where they hold a
  deleted file's. HFS+ (published, `hfs_readwrite.c`,
  `hfs_vnop_write`) sets the size back to the size before the write
  when `cluster_write` fails, unless it is EAGAIN: a cut write leaves
  nothing, as measured (section 7). Linux's `generic_perform_write`
  stops between folios on a fatal signal and the size follows the
  pages copied: a prefix, as measured (section 8).
* **Hypothesis, not tested**: the copy fails because the process that
  SIGKILL ends loses its memory while its writing thread still copies
  from it; a kill found between pieces gives (a). Why a force makes (b)
  the usual outcome is not known.


## 10. For 028-60's part 2

* **Other systems**: on s1 (Linux, ext4) a kill left a prefix of the
  cut write in 1,574 of 2,981 kills that found one, never zeros; on
  HFS+ nothing of it. Both are what the start recovers today as a cut
  tail. The cut is needed for APFS, macOS's file system: there a kill
  that finds a write of more than one page can leave zeros within the
  length, with FileStream's hard sync more often than a prefix.
* **The file ends at a page boundary**: in all 53 cut files on APFS
  (35, 16 and 2 on three devices) the length is a multiple of 16,384,
  where the page by page copy stopped (section 9). B2 can require
  that the last file's length be a multiple of 4,096, which covers 16
  KiB pages (Apple silicon) and 4 KiB (Intel Macs).
* **The zeros start at a page boundary**: in all 53, the wrong bytes
  begin on a multiple of 16,384. In a stream they begin at or before P,
  the position whose size reads 0, as P is the first record start
  inside them. B2 does not see where they begin when the record's own
  bytes before them are zero, but it can require that every byte from
  the 4,096 boundary at or before P to the end be zero, in the file's
  offsets (a stream file's first position, its name times 100,000, is
  not a multiple of a page). That holds for every zeroed file
  measured, as their zeros begin on a page boundary at or before P,
  and narrows B2 to them: zeros that begin inside a page after P are
  refused as in B1.
* **The bound**: the zeros measured lie within one piece of the kernel
  (at most 62 pages on the internal SSD, 126 on the RAM disk, 114 on
  the image) and within the cut write; the piece is at least 1 MiB and
  at most 64 MiB (`MAX_UPL_SIZE_BYTES`), the write at most 5 MB
  (026-07). 028-60's bound of 8 MB covers every case seen.
* **Old bytes**: on the RAM disk and the disk image, 7 cut files held
  a deleted file's bytes within the length, not zeros. B2's zero check
  does not take them. What the start does with them today depends on
  what its walk reads there: a size that is not valid is refused as in
  B1; but in BergDB the deleted file is an earlier stream file (a cut
  deletes files, a new file may get their blocks), whose bytes are
  records and meta blocks, and read where the stream's tail should be
  they could be taken for the stream's own. None of B1 to B3 is about
  this. Not seen on F53's internal SSD. For 028-60's owner: a case of
  its own, to be judged (whether the start can tell another file's
  records and meta blocks from its own).
* **Recommendation**: B2, with four conditions, each measured to hold
  for every zeroed file: every byte from the 4 KiB boundary at or
  before P to the end is zero; the last file's length is a multiple of
  4,096; P is in the last file; the run is at most 8 MB. Else B1's
  refusal. And the case of old bytes to 028-60's owner, as above.


## 11. State

2026-11-26, by an agent of lead-1126.

* **Done:** section 3's parts 1 to 6: the probe (section 4), the
  environments (5), F53's internal SSD (6), other file systems on F53
  (7), s1 (8), the cause as far as measured and read in the published
  source (9), and the meaning for 028-60's part 2 with a
  recommendation (10).
* **Kept:** each run's TSV file and summary, and a few cut files
  (zeroed and with old bytes) with the end of their logs, outside the
  repository; the lead can ask for them. The disk images and the RAM
  disks were detached and deleted; nothing of the probe is left on s1.
* **Not settled:** why a kill makes the copy fail (section 9's
  hypothesis); why a force makes zeros the usual outcome; why small
  files (8 MiB) gave no cut write; whether F53's internal SSD can show
  a deleted file's bytes as the RAM disk and the image did; a power
  loss, and systems other than F53 and s1.
* **Next:** Frans's decision on 028-60's part 2, with section 10; the
  case of old bytes for 028-60's owner.


## 12. What BergDB does: the zero-tail cut

Frans decided on 2026-11-26, for 028-60's part 2: one rule on every
operating system and file system, with no detection of either. At the
open, `FileStream` leaves a run of zero bytes of at most 8 MB at the
end of its last file out of the stream; its first append truncates the
file where the run starts and forces it. Nothing above `FileStream` changed; the layers above see a
stream cut short, a prefix of what was appended (014-01, section 7),
and the start's recovery completes and aborts the torn last record. The
code, its tests and the runs are in 028-60 (sections 7 to 10).

* **Why one rule.** The cut's safety rests on BergDB's own format, not
  on a file system's behaviour: a committed record and a valid meta
  block end in the byte 10, so zeros at the end of the last file are
  the system's, or part of a torn record that recovery aborts. No
  committed transaction can be among them, on any system.
* **The bound.** 8 MB covers every zeroed tail measured here (section
  10: within one piece of a write, the write at most 5 MB). It limits a
  silent repair in the case outside the contract, a power loss that
  destroyed forced bytes and left zeros in their place; a longer run is
  left, and the start takes it as before.
* **Section 10's alignment conditions dropped.** The 4 KiB boundary at
  or before P and the last file's length a multiple of 4,096 are a
  fingerprint of APFS, not part of why the cut is safe.
* **Stale bytes that are not zero** (section 10, "Old bytes"; 035-02)
  are not removed: the start refuses them as before, and they are
  handled apart, in 028-67.


## Log

2026-11-26. Created (Frans), in 035.

2026-11-26. Parts 1 to 6 by an agent of lead-1126, in the clone c351
(branch `035-01`): `probes/ZeroTailProbe.java`; 21,200 kills on F53's
internal SSD, 8,400 on other file systems of F53, 6,800 on s1. On APFS
a kill that finds a write of more than one page can leave zeros within
the length (35 files), each from a page boundary at the start of the
kernel's piece of the write (1 MiB on the internal SSD) to a page
boundary inside it, short of the write's end; on a RAM disk and a disk
image some such pages held a deleted file's bytes. Writes of one page
or less were never cut. s1 (ext4) and HFS+: prefixes or nothing, no
zeros. Recommendation for 028-60's part 2: B2 with four conditions
(section 10).

2026-11-26. Section 12: what BergDB does, the zero-tail cut in
`FileStream` as Frans decided it for 028-60's part 2 (one rule on every
system, at most 8 MB, no alignment conditions; stale bytes in 028-67).
