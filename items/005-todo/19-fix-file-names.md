005-19. Fix: FileStream cannot reopen a stream past 214.7 TB
============================================================

Status: open. Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in a review of the Java code for overflow, by Claude
(Opus 5.5, Claude Code), at Frans's request; checked with a probe.


The issue
---------

A `.bergdb` file is named by its first stream position divided by 100,000,
in 14 digits, written from a `long`, but `FileStream.stringToIndex` parses
it with `Integer.parseInt`. Past 2^31 × 100,000 bytes (214.7 TB) of stream
positions, the stream is written but cannot be opened again:
"BadDirStateException: Bad name of bergdb file". Positions are never reset
(reclaim cuts the front only), so at 50 MB/s of stream writes this comes
after about 50 days.


The fix
-------

Parse the index as a `long`.


Done when
---------

* A unit test: a stream at position 2^31 × 100,000 (`seekFirstPos`) is
  written, closed and opened again.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.
