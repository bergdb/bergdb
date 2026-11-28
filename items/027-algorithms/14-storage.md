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
  until 2026-11-26), and at least 1 MB once that stream is 4 MB
  (2026-11-28, 028-73); a larger size begins only at a length that is a
  multiple of it, a smaller one at once. A cut deletes whole files
  only, those that end before its position, never the last one, on a
  thread of the storage's own (005-46), a batch at a time with one
  force of the directory after it (028-66). So the disk can hold up to
  about one file more than the stream, about a tenth of the stream when
  that file was made, or 1 MB when 4 to 10 MB were kept, also after the
  stream has shrunk (RB-011), and,
  for a while after a cut, the files not yet deleted (027-13, section
  4). A start accepts files of any sizes beside each other, the
  quarter's beside the tenth's: it checks that each file begins where
  the one before ends, or after a gap (below), and that every file but
  the last is a multiple of 100,000 bytes (`testMixedFileSizes`). A new
  database writes 20 files of 200 kB up to 4 MB and 1 MB files from
  there, as with the quarter. With per-append forcing each new file
  costs `BufferedStream`'s thread the force of its predecessor's last
  piece, the new file's and the directory's, about 10.5 ms on F53. With
  the tenth alone (2026-11-26 to 2026-11-28) a new database wrote its
  first 10 MB in 50 files of 200 kB, and a fast load's longest wait for
  room in the write buffer was 144 to 282 ms in six runs, 0 to 16 ms on
  release 2026.6; with the floor of 1 MB, 1 wait of 7 to 21 ms in four
  runs, against 145 to 169 ms on `main` then: measured (028-73).
* **A backup by a copy of the files.** A file is changed only by
  appends at its end and removed only whole, the deletes issued oldest
  first; no file
  is renamed, and no byte written twice but in one case: the first
  append after an open that left a tail of zeros out of the stream
  truncates the last file where the zeros begin and writes there
  (below). A copy of the `*.bergdb` files of a stopped database is the
  database. A copy of a running one that lists the files and copies
  them in the order of their names, the last one last, is the stream as
  a kill of the process would leave it when the copy read the last
  file's end, and starts as
  after a kill; a file that a cut deletes while it is read stays
  readable on macOS and Linux, and the copy then holds files that the
  stream has deleted, as after a crash before a cut's deletes. A listed
  file that a cut deleted before the copy opened it is missing: with a
  gap, the copy opens from the file after it (below); without its first
  files, from its first file. Either can lack the record of the cut
  that deleted them; a start then refuses it, as its first position is
  after its cut, and the copy must be taken again; a start that takes it
  deletes the files before the gap (028-66). Checked on F53 by 028-62's
  `BackupCopy` probe: 100 copies of a database written all the time,
  with cuts, each started and holding the state after one of its
  transactions; 29 taken again. With the gaps of 028-66, by its
  `BackupGap` probe (`BackupCopy` that goes on past a listed file that a
  cut deleted, on the rule of the files before a gap; 028-66, section
  6.4): 100 copies, 45 whole, 41 with a gap (5 started, 36 refused), 14
  without their first files (14 started); each started copy held the
  state after one of the writer's transactions, and each refusal said that
  the stream lacks bytes. Windows not run: a delete of a file that
  a copy program holds open can fail there, which fails the stream. A
  copy that overlaps the first append after an open that left zeros
  out (after a kill, or of a copy that ended in zeros) can hold the old
  file's zeros in place of bytes written after them, and is not a
  backup (Codex's reviews of 028-60, part 2). So a copy begins after an
  append of at least one byte since the open has returned (an append of
  nothing does not cut the zeros), or after `close()` has returned:
  for a running database, after a transaction that changed something,
  committed since the start, and a `sync()` that returned after it (a
  commit alone can return before its bytes reach `FileStream`); for a
  stopped one, after its `close()` has returned (`stop()` returns
  before the close ends).
* **A gap in the files** (028-66, 2026-11-27, from the principle that
  Frans decided that day: the stream is the bytes from reclaim's cut to
  the end, and what the storage still holds before the cut belongs to
  the storage's implementation). The cut's
  thread deletes a batch of files, the deletes issued oldest first, and
  then forces the directory once; until 2026-11-27 it forced the
  directory after each file, and a writer with hard sync at full speed
  wrote about 40 % slower with the tenth's files (028-66, section 1). No
  order of the deletes on the device is assumed: a power loss can keep
  the delete of a newer file and lose that of an older one. So the open
  takes a gap in the files' sequence, a file that begins after the end
  of the one before it: the stream is the files after the last gap, its
  first position the first of them's; the files before, the leftovers,
  are not read as the stream, and the first cut at or after the first
  position deletes them, oldest first, before its own files, once they
  have been checked (below). Why it is safe: a file is
  missing only if a cut deleted it, and the thread deletes only after
  the stream is forced up to its length at the cut (`forceTo`), which
  holds the table that decided the cut, durable before the cut was made
  (027-13, 1.7). So the gap's end is at or before the cut of the durable
  table; a start reads nothing before that cut (027-11, section 1.10),
  finds it at or after the first position, and cuts there, which deletes
  the leftovers (027-13, 1.9). A first position after the cut means
  missing bytes of the database: a file removed by hand, a copy that
  missed files; the start refuses, with the storage's account of the
  gap, and deletes nothing.
* **The files before a gap must be the database's** (Frans, 2026-11-27;
  028-66, with 028-67's C3). What: a file before a gap is deleted only
  if its first meta block, the first whole block at or after its start
  (every file of `FileStream`'s begins at one), is of this version,
  valid, holds its own position (offset 46) and the database ID of the
  stream's first block (offset 24); else the start is refused, before
  anything is written or deleted, with a `StreamIoException` whose
  cause is a `BadDirStateException` that names the file, what its block
  holds, the gap and the way out: move the files before the gap out of
  the directory, and keep them. When: at each start, in
  `RecoverableStream.recover()`, after the last valid meta block is
  read and before the walk of the tail. By whom: `FileStream.
  checkLeftovers()` gives each leftover, oldest first, with a reader of
  its bytes on a channel of its own; `RecoverableStream.leftoverProblem`
  checks its block; `BufferedStream` and `StorageManager` pass the call
  on (`AppendOnlyStream.checkLeftovers()`, a default that holds none).
  `FileStream` deletes no leftover before a call that found them all to
  be the stream's own, so a stream under a wrapper that does not pass
  the call on keeps them. Refused so: another database's file, a file
  of meta version 155 (release 2026.6), a damaged first block, a file
  of zeros, a file with no whole block; before 2026-11-27 (028-66's
  first build) such files were deleted when the stream after the gap
  held its cut after the gap's end. Not refused: an older copy of a
  file of the same database, whose blocks hold the same ID and their
  own positions; it is deleted. How it is checked: the tests below.
  Tests: `FileStream.
  testRestartMissingFile` (no cut deletes an unchecked or a refused
  leftover), `testRestartRefusedOverlap`, `testGapsAtOpen`,
  `testCutDeletesABatchWithOneDirectoryForce`;
  `FileStreamPowerLossTester.testRecoveryAfterEverySubsetOfABatch`,
  `testUnorderedUnforcedDeletionsLeaveAGapThatOpens`,
  `testStartRefusesAStreamThatLacksBytes`,
  `testStartDeletesTheDatabasesFileBeforeAGap`,
  `testStartRefusesAFileBeforeAGapThatIsNotTheDatabases` (the files
  compared byte for byte after each refusal), and the traces, whose images of
  unforced deletes in any combination must start, hold every
  acknowledged commit and delete the files before the gap;
  `flush-order.sh` (deletes in name order, each after the files that
  survive it are forced, a directory force after the last).
* **A tail of zeros** (028-60, part 2; RB-012). At the open, after the
  directory's lock and the check of the files' names and lengths and
  before anything reads the stream, `FileStream` leaves a run of zero
  bytes of at most 8 MB (`ZERO_TAIL_MAX`, 8,000,000) at the end of its
  last file out of the stream (`zeroTailLength`): the stream's length
  ends where the run starts, reads stop there, and the last file's size
  class is computed from its length without the zeros. The open does
  not change the file. The first append truncates it where the run
  starts (`FileStreamIo.truncate`) and forces it (`ZERO_TAIL`), also
  with per-append forcing off, before its check of the file's length
  and its write; so does a cut that deletes files before it
  (`pretruncate`: else a last file of zeros only, left as the only
  file, would be taken whole by the next open); `close()` and an
  append of nothing do not. So a start
  refused before it writes (another node size, an unsupported version,
  bytes that are not a BergDB stream's, as an earlier release's
  encryption: "The start has written nothing") leaves the files as they
  were; a recovery may append before a later check refuses a start,
  and then the cut is made. A longer run is left, and so is a stream
  whose only file is all zeros (a repair never empties a stream); a
  start refuses the latter, up to 200,000 bytes, as a creation that did
  not complete (`DatabaseNotCreatedException`; 028-80, 2026-11-28). The same rule on every operating system and file system,
  with no detection of either (Frans, 2026-11-26). The layers above see
  a stream cut short, a prefix of what was appended (014-01, section 7),
  and recovery completes and aborts the torn last record (027-11, 1.3);
  nothing above `FileStream` changed. Safe for the stream format: a
  committed record and a valid meta block end in the byte 10 (027-03),
  so zeros at the end of the last file are the system's, a torn
  record's that was never synced, or a recovery's zeros of an aborted
  record, which the next recovery writes again. The bound limits a
  silent repair in the case outside the contract, a power loss that
  destroyed forced bytes. It holds for a kill whatever the buffer above:
  `FileStream` hands the system at most 5 MB in one write (`WRITE_MAX`;
  028-80, 2026-11-28), a longer append in pieces with one force after
  them, and a kill's zeros are where the bytes of the write that it cut
  should be. Until then the bound rested on `BufferedStream`'s writes,
  at most half its buffer, 5 MB with the default of 10 MB, and the Core
  API's `DbBuilder.stream` takes any size: from 16 MB a write could pass
  8 MB (033's review of the start, F4). Not removed: bytes that are not zero (028-67).
  The rule holds for every stream that `FileStream` opens, with no way
  to turn it off; BergDB has no encrypted stream since 028-69
  (2026-11-27). Tests: `FileStream.testZeroTailRemoved`,
  `testZeroTailLastFileOnly`, `testZeroTailCutAtFirstAppend`,
  `testZeroTailFileSize`, `testZeroTailCutBeforeFirstAppend`,
  `testWritesAtMostWriteMax`; `DbTesterStream.testZeroedTailOverMetaBlock`,
  `testRefusedStartsKeepZeroTail`, `testCreationLeftAsZeros`;
  `PubTester.testEncryptedByAnEarlierReleaseRefused`.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-26. The files and the disk, and a backup by a copy of the
files, recorded from the code before the part is written (028-62).

2026-11-26. A tail of zeros: `FileStream`'s open leaves one of at most
8 MB at the end of its last file out of the stream, and the first
append cuts it from the file (028-60, part 2, after Codex's review);
the backup's one exception to appends only.

2026-11-27. The tail of zeros on `main`, for every stream, with no
opt-out: the internal encryption is gone (028-69; 028-60, part 2).

2026-11-28. Checked against the code at 8a0897cf (031-06's landing and
028-66's option C on `main`): the recorded points stand, among them the
gap in the files and the rule of the files before it, which 028-66's
commits recorded on 2026-11-27; added the cost of the tenth's files at a
new database's first 10 MB (028-73) and the backup copies with gaps,
028-66's `BackupGap` on that rule. By an agent of lead-1127, on the
branch `031-06-docs`.

2026-11-28. New files at least 1 MB once the kept stream is 4 MB, the
tenth unchanged above 10 MB (028-73, Frans's option (b)): the points on
the files, the disk and a new database's first 10 MB.

2026-11-28. 028-80: `FileStream` writes at most 5 MB at a time, so the
zero tail's bound holds for every buffer; the only file all zeros is
refused as a creation that did not complete. By an agent of lead-1127,
on the branch `start-fixes`.
