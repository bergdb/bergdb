# 027-14. Storage and durability

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 10 of 027's outline (027-04, section 2.3; levels: all). Below the
Core: the append-only stream's contract; `FileStream`'s files and forces;
`BufferedStream`'s chunks and group commit; the meta blocks; what
`sync()`, `stop()` and `close()` promise; the physical cut's deletes; the
crash contract (a prefix of what was appended); per-append forcing turned
off; no replication, copies left to the OS.

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.

Recorded before the part is written (028-62, 2026-11-26), from the code;
`FileStream`'s Javadoc states them:

* **The files and the disk.** `FileStream` keeps the stream in files of
  200 kB, 1, 5, 20, 100 and 500 MB, 2, 10, 50 and 200 GB, each named by
  its first position. A new file gets the largest size that is at most
  a tenth of the stream that the files hold when it is made (a quarter
  until 2026-11-26); a larger size begins only at a length that is a
  multiple of it, a smaller one at once. A cut deletes whole files
  only, those that end before its position, never the last one, on a
  thread of the storage's own (005-46). So the disk can hold up to
  about one file more than the stream, about a tenth of the stream when
  that file was made, also after the stream has shrunk (RB-011), and,
  for a while after a cut, the files not yet deleted (027-13, section
  4). A start accepts files of any sizes beside each other, the
  quarter's beside the tenth's: it checks that each file begins where
  the one before ends and that every file but the last is a multiple
  of 100,000 bytes (`testMixedFileSizes`).
* **A backup by a copy of the files.** A file is changed only by
  appends at its end and removed only whole, the oldest first; no byte
  is written twice, no file truncated or renamed. A copy of the
  `*.bergdb` files of a stopped database is the database. A copy of a
  running one that lists the files and copies them in the order of
  their names, the last one last, is the stream as a kill of the process
  would leave it when the copy read the last file's end, and starts as
  after a kill; a file that a cut deletes while it is read stays
  readable on macOS and Linux, and the copy then holds files that the
  stream has deleted, as after a crash before a cut's deletes. A listed
  file that a cut deleted before the copy opened it is missing: the copy
  must be taken again (with a gap, a start refuses it; without its first
  files, it can lack the record of their cut). Checked on F53 by 028-62's
  `BackupCopy` probe: 100 copies of a database written all the time,
  with cuts, each started and holding the state after one of its
  transactions; 29 taken again. Windows not run: a delete of a file that
  a copy program holds open can fail there, which fails the stream.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-26. The files and the disk, and a backup by a copy of the
files, recorded from the code before the part is written (028-62).
