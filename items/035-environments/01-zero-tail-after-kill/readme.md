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

Not tested. The kernel (XNU) copies a large write into the page cache
in chunks of pages, and moves the file's end to a chunk's end, a page
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


## Log

2026-11-26. Created (Frans), in 035.
