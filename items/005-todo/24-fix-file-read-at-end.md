005-24. Fix: a FileStream read at the end of the stream loops forever
=====================================================================

Status: open. Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in the review of the Java code for overflow (not an
overflow), by Claude (Opus 5.5, Claude Code), at Frans's request; checked
with a probe.


The issue
---------

`FileStream.DbFile.read` checks `spos > spos + fileLength`, which is never
true; `this.spos` was meant. A read that starts at the end of the last file
reads 0 bytes, and `FileStream.read` tries again forever (the probe's reader
still ran after 3 s); a read further on throws `IndexOutOfBoundsException`
from `readFully`. Nothing reads there in normal operation, but a bad
position (a corrupt pointer) would hang a reader.


The fix
-------

Check against `this.spos + fileLength`, and make `FileStream.read` throw an
`IOException` (EOF) when a read goes past the end of the stream, without
marking the stream as faulty.


Done when
---------

* A unit test: reads at and past the end throw, and the stream is still
  usable.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.
