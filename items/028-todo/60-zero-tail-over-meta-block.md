028-60. Fix: after a kill, a zeroed tail over a meta block stops the start
=========================================================================

Status: done (2026-11-27): part 1 (2026-11-25, the branch `028-60`: a
meta block of zeros is not valid) and part 2 (made 2026-11-26 on the
branch `028-60b`, revised after Codex's two reviews, section 10;
rebased on 028-69 without its opt-out for encrypted streams on the
branch `028-60c`, 2026-11-27, section 11): `FileStream`'s open leaves
a tail of zeros out of the stream, and its first append cuts it, for
every stream. Kind: Fix. Frans: decided (2026-11-26, section 7;
2026-11-27, the removal of the internal crypto code, 028-69).
Created 2026-11-25 by Frans Lundberg.

What: 031-02's app hunt, finding F1 (section 5): three times in about
9,500 kills of a writing process (SIGKILL, macOS, APFS), the last stream
file ended in zeros within its length, from a page boundary on (115 to
459 kB). Where the zeros cover a meta block's position, the next start
throws `StreamFormatException: Invalid magic bytes in stream: ... not a
BergDB stream, or it is damaged; or an earlier release ... encrypted
it` (from `Db.refuseOtherNodeSize`, which reads the last meta block
before recovery), and the database does not start until a person cuts
the file; cut at the record that the zeros reach, it starts with every
transaction a sync returned for. A zeroed tail that ends before the
next meta block is recovered as a cut tail. The system makes the zeros
(031-02's `ZeroTailProbe`: plain `RandomAccessFile` appends and forces,
1 in 150 kills). Release 2026.6 refuses the same files.

Why: the Javadoc of `Database` ("What a crash keeps") says that a crash
cuts the stream's tail and the start recovers it; only a power loss is
said to leave a tail of zeros, refused with "Bad transaction size in db
stream, S, spos P" and the advice to cut at P. A database that does not
start after a process kill is S2 (033's rules); in 2026.6, a released
bug.

Frans: decision: part 2, what a start does with zeros that reach past a
record's end (section 4, options B1 to B3, with a recommendation).

Done when: the refusal reproduced from the kept files and from a unit
test (a zeroed tail over a meta block, on a file stream); its cause
named in the start's order of reads; a fix with which such a tail is
recovered as the Javadoc says, or, if that needs a choice of what the
start may take as a cut tail, the options written here; a unit test
that fails before the fix; `java/before-commit.sh` printing `BEFORE
COMMIT OK`; the kill-restart harness (`java/stress/kill-restart.sh`)
and 031-02's KillWriter run; an RB entry drafted for 033.

First step: 031-02, section 5, F1; `Db.refuseOtherNodeSize` and the
start's recovery of a cut tail (027 parts on the stream and startup:
027-03, 027-11); the Javadoc of `Database` and `FileStream`.


Result
------

### 1. The kept files

The files as the kills of 031-02 left them (seeds 63 and 91), started on
copies (2026-11-25). Positions are stream positions; a file's first
position is the number in its name times 100,000.

* **Seed 91.** The last file, `00000000189400.bergdb`, 14,893,056 bytes,
  is zero from 14,778,368 (stream 18,954,778,368, a 16 KiB page) to its
  end, 114,688 bytes. The meta block at 18,954,800,000 is 128 zero
  bytes; the one at 18,954,600,000 is valid and names the record at
  18,953,771,760 (240 bytes). The next record, at 18,953,772,000, has
  its size, 1,424,872, before the zeros, and reaches to 18,955,197,768,
  past the end: the zeros are inside the last record.
* **Seed 63.** The last file, `00000000093350.bergdb`, 4,374,528 bytes,
  is zero from 3,915,776 (stream 9,338,915,776) to its end, 458,752
  bytes, over the meta blocks at 9,339,000,000 and 9,339,200,000. The
  valid block at 9,338,800,000 names 9,337,216,288; the records from
  there are of 512, 1,684,496, 320 and 194,968 bytes; the last, at
  9,338,902,640, has its size before the zeros, which begin 13,136 bytes
  into it, and ends at 9,339,097,736, inside the file: there the next
  record's size is 0. The zeros reach past a record's end.
* **Before the fix**, main at `cbf0a7e0` and release 2026.6 (`bbcd802f`,
  built in a worktree of its tag) refuse both: `StreamFormatException`,
  "Invalid magic bytes in stream: the stream is not a BergDB stream, or
  it is damaged; or an earlier release of BergDB, 2026.3 or before,
  encrypted it ...", cause `BadMagicBytes ... got: 00000000`; the files
  are not changed.

### 2. The cause

* A start reads the last valid meta block before it writes: first
  `Db.refuseOtherNodeSize` (005-50: a start with another node size
  writes nothing), then `RecoverableStream.recover()` itself (005-40: a
  wrong key or version writes nothing). Both call
  `readLastValidMetaBlock()`, which reads the blocks from the last one
  complete in the stream down to the first valid one, by
  `readMetaBlock()`. That read threw `BadMagicBytes` for any first four
  bytes but "berg", zeros too, where a block that a crash cut, its last
  byte not 10, is read as not valid and passed over. So a zero block
  among the last bytes stopped the start before the recovery; the order
  of the two reads does not matter, as `recover()` reads the same way.
* The recovery of the tail (`fixLastTransactionIfNeeded`) walks from
  the record that the last valid block names, by the records' sizes. It
  reads only the size field at each record's start. Zeros inside the last
  record are not read: the record's size, before them, reaches to or past
  the stream's end, and the record is completed with zeros and aborted
  (its last byte 0). Zeros at a record's start give the size 0, refused:
  "Bad transaction size in db stream, 0, spos P". So "a zeroed tail that
  ends before a meta block is recovered" (031-02, F1) holds where the
  zeros begin in the last record, as in seed 91 and, by the walk, in the
  9 zeroed tails that the hunt's starts took; zeros that reach past a
  record's end, as in seed 63, are refused with that message, a meta
  block among them or not.

### 3. Part 1, the fix: a meta block of zeros is not valid

`RecoverableStream` (2026-11-25):

* `readMetaBlock()` reads a block of 128 zero bytes as one that is not
  valid (its last byte is 0), as a block that a crash cut; the readers
  pass over it to the valid block before it. Any other bytes than the
  magic ones still throw `BadMagicBytes`. This extends what the start
  already does for a block that a crash cut, and for zeros inside the
  last record: the start reaches its recovery, which takes the tail as
  a cut tail or refuses it as `Database`'s Javadoc says.
* `fixMetaBlockIfNeeded()`, which completes a block that the stream's
  end cuts, completes one whose bytes are zero as far as they go with
  zeros, not with `FILL_OUT_TEMPLATE`'s magic bytes and version: with
  the template after 1 to 7 zero bytes, the block was neither a block
  nor zeros, and a later read of it, as the next start's when no valid
  block follows it, refused the stream.
* Javadoc of `recover()`, `readLastValidMetaBlock()` and `readMetaBlock()`;
  027-03 (section 6's checks on reading, section 7's recovery) and
  027-11 (1.2, step 3; 1.3).

With the fix (the release jar of the branch):

* **Seed 91 starts**, at k = 122,334, its whole state equal to KillWriter's
  oracle at 122,334 (every key, object, index scan both ways, counter),
  and again after a second start. The recovery completed the last
  record (the file is then 15,197,768 bytes) and aborted it. No sync had
  returned for that record or after: its bytes were not on the disk.
* **Seed 63 is refused** as the Javadoc says, "Bad transaction size in db
  stream, 0, spos 9339097736. Stream length: 9339374528.", with nothing
  written. Cut as the Javadoc says, the file to 9,339,097,736 less
  9,335,000,000, 4,097,736 bytes, it starts at k = 56,280, the last
  transaction a sync returned for (031-02, F1), its state equal to the
  oracle's, twice. Release 2026.6 refuses the same cut file with
  "Invalid magic bytes": before the fix, the documented way out did not
  work when the zeros covered a meta block.

Tests (each fails before the fix, at `cbf0a7e0`):

* `DbTesterStream.testZeroedTailOverMetaBlock` (an f-test, about 0.3 s):
  a file database whose last file, of 1 MB from 4,000,000, ends in a
  record of 400 kB over the meta blocks at 4,400,000 and 4,600,000; the
  file zeroed from the first 16 KiB page after the record's header to its
  end, with its length as it is and cut inside the record. Both start
  with the records before, the zeroed one gone, and write and start
  again. Zeros from inside the record before it, over two records'
  starts, are refused with "Bad transaction size in db stream, 0, spos
  P", nothing written, and the file cut at P starts. Before the fix all
  three threw "Invalid magic bytes in stream".
* `RecoverableStream.Tester.testZeroedTailOverMetaBlocks`: the same on a
  `MemoryStream`, with a read that begins at a zero block and a later
  append and recovery (before: `BadMagicBytes`).
* `RecoverableStream.Tester.testZeroedTailEndingInMetaBlock`: a zeroed
  tail that ends 0 to 127 bytes into a block's position; the block
  completed with zeros (the template at 0), and a second recovery
  (before: `BadMagicBytes` at 1 to 127).

### 4. Part 2, for Frans: zeros that reach past a record's end

After part 1, a kill on macOS that leaves zeros past a record's end, as
in seed 63, gets the documented refusal and its way out, but the database
does not start until a person cuts the file. `Database`'s Javadoc says
that a crash's tail is recovered, and names a tail of zeros only after a
power loss. Taking such a tail changes what a start takes as a cut
(014-01, section 7: a start recovers only a truncated tail, and the
storage keeps a prefix of what was appended), so it is a choice. What is
known:

* The zeros seen are the bytes of the write that the kill cut, from a
  page boundary on, within the file's length (031-02, `ZeroTailProbe`,
  without BergDB); why the system leaves them is not settled (031-02,
  section 7). The bytes before them are right. A
  write of `BufferedStream`'s thread to `FileStream` is at most half its
  largest buffer, 5 MB (026-07); the zeroed tails seen were 115 to 459 kB.
* No transaction that a sync returned for was among the zeros in the
  cases seen (seed 63: the last synced, 56,280, is before P), and none
  can be when the zeros are bytes of the write that the kill cut: a sync
  returns only after the write that holds its record has returned, and
  with the hard sync, the default, its force. The same after a power
  loss with the hard sync, on a file system that keeps what it forced.
* A committed record ends in the byte 10, and so does a valid meta
  block: neither can lie inside a run of zeros. Every record that ends
  before the zeros is as it was written; the one that the zeros begin
  in, if they begin inside a record, ends at P, the position whose size
  is 0, with its last byte 0: aborted.
* How often: three of about 9,500 kills of KillWriter, whose records are
  up to 1.6 MB; ZeroTailProbe 1 in 150 with writes of 64 kB to 2 MB.
  Zeros past a record's end need a write of more than one record, as a
  burst of commits or a sync after many records gives. Linux and other
  systems were not tried (031-02, section 7).

The options:

* **B1. Refuse, as documented (the state after part 1).** The start
  refuses with "Bad transaction size in db stream, 0, spos P. Stream
  length: L." and writes nothing but the missing bytes of a meta block
  that the end cut, if any; a person keeps a copy, cuts the file
  that holds P to P less its first position and removes later files
  (`Database`'s Javadoc); the database then starts with every
  transaction a sync returned for. To do: `Database`'s "What a crash
  keeps" and `FileStream`'s Javadoc say that on macOS (APFS) a kill of
  the process during an append can leave such a tail too, not only a
  power loss; the message says that the stream ends in zeros from P and
  how to cut, as U8-3 (020-24-08) asked. About 20 lines, no new code
  path. Cost: a database that does not start after a kill until a
  person cuts a file, documented. Risk to data: none.
* **B2. Take a tail of zeros as a cut tail, by cutting it.** When the
  recovery's walk meets the size 0 at P, and every byte from P to the
  stream's end is zero, P lies in the last stream file, and the run is
  at most a bound (8 MB: one write of the buffer's thread is at most 5
  MB), recovery cuts the stream at P and ends as for a cut tail; else it
  refuses as B1. The cut needs a new operation of the storage layer, a
  cut of the tail at recovery: `AppendOnlyStream` gets it, `FileStream`
  truncates its last file and forces it, `MemoryStream` and
  `BufferedStream` (before its first append) pass it on, the others
  refuse it; the stream contract's tests and a kill test cover it. A
  start then writes a cut where today it writes only a fill (the
  aborted record's zeros); a start refused later, as the fill, keeps it.
  `Database`'s Javadoc: a crash's or a kill's tail of zeros after the
  last record is taken as a cut tail; 014-01, section 7, records the
  change. About 150 lines with the tests. Cost: a new storage operation
  and a contract change. Risk: a storage that loses forced bytes and
  leaves zeros in their place, outside the contract (014-01, section 7),
  is no longer refused: the start takes the prefix, as it takes a cut
  tail that took synced transactions today without an error
  (`Database`, "The files").
* **B3. B2 on request only.** The default refuses as B1, with a message
  that names a setting of the builder (such as `cutZeroTail()`) that
  makes the next start do B2's cut. Cost: B2's work and a new method in
  the Pub API, which is stable; a user still meets the refusal once
  after a kill. Risk: as B2, for the starts that ask.

Recommendation: B2. The zeros are a failure of the provider to keep a
prefix of what was appended after a kill, which 014-01, section 7, puts
on the provider, and `FileStream` is BergDB's own (its point 4 (b));
the cut removes only zeros, which can hold neither a committed record
nor a transaction a sync returned for, within the last file and a bound
of one write; and it keeps the Javadoc's promise for a kill without a
person's work. B1 is enough for a release that documents the case, as a
known issue, until B2 is made.

### 5. Release 2026.6 and the C port

* Release 2026.6 has part 1's bug: it refuses both kept files, and seed
  63's file cut at P (section 3). Every release since 2026.1 has the same
  check of the magic bytes in `RecoverableStream.readMetaBlock`, by its
  source; only 2026.6 was run.
* The C clone (item 012, a separate project, following release 2026.2)
  has the same check (`rstream.c`, `BadMagicBytes`); not changed here.

### 6. Gates

On the branch `028-60` (on `cbf0a7e0`), macOS, JDK 27, 2026-11-25, beside
`week.sh` and other sessions' runs:

* The three tests of section 3 fail before the fix and pass after it.
* `java/before-commit.sh`: BEFORE COMMIT OK (92 s; unit 1,754, f 90).
* `java/stress/kill-restart.sh 200`: SELF-CHECK OK (the four planted
  faults found), LATE EXIT OK, KILL RESTART OK: 200 kills and 7 exits
  in 305 s, seed 20261125.
* 031-02's KillWriter, `-DnoSd=true`, on the branch's release jar: seed
  63, 250 kills, KILLWRITER OK (199,865 transactions, 523 older states,
  every check of each recovery passed), and seed 91, 250 kills,
  KILLWRITER OK (207,693 transactions, 532 older states); no zeroed tail
  came in these 500 kills (three in about 9,500 in 031-02).
* The kept files: seed 91 starts with its whole state (k = 122,334);
  seed 63 is refused as documented and, cut at P, starts at k = 56,280,
  the last synced (section 3).

### 7. Decision for part 2 (Frans, 2026-11-26)

Neither B1, B2 nor B3 as written. The repair lives in `FileStream`
only, the same rule on every operating system and file system, with no
detection of either: at open, `FileStream` removes a run of zero bytes,
at most 8 MB, at the end of its last file (it truncates the file where
the run starts and forces it). Nothing above `FileStream` changes: no new
method in `AppendOnlyStream`, no change in `RecoverableStream`. The
layers above then see a stream cut short, a prefix of what was appended
(014-01, section 7), and the existing recovery completes and aborts the
torn last record.

* **Why it is safe:** a complete record and a valid meta block end in
  the byte 10, so zeros at the end of the last file are the system's or
  part of a torn, never-synced record.
* **The bound:** 8 MB limits a silent repair in the case outside the
  contract, a power loss that destroyed forced bytes.
* **Not part of the rule:** 035-01's 4 KiB alignment conditions
  (dropped: a fingerprint of APFS, not part of why the cut is safe), and
  stale bytes that are not zero (028-67, separate).

### 8. Part 2, the fix

On the branch `028-60b` (on `27548f13`), 2026-11-26:

* **Where it runs.** `FileStream`'s constructor: after
  `createDirIfNeeded()`, `lockDir()` and `checkDbFiles()` (the files'
  names and lengths), in `openForRw()` of the last file, right after
  `FileStreamIo.open()`. Nothing reads the stream before it:
  `RecoverableStream`, `Db.refuseOtherNodeSize` and the recovery come
  after the constructor. `zeroTailLength()` reads the file backwards in
  pieces of 64 KiB until a byte that is not zero or 8 MB + 1 zero bytes;
  a run of 1 to 8,000,000 bytes (`ZERO_TAIL_MAX`, decimal as the class's
  sizes) is left out of the stream: the last file's length in the
  stream (`DbFile.fileLength`) and the stream's length end where the run
  starts, so reads stop there, and the last file's size class, its
  room for appends, is computed from that length. A run of zeros over
  8 MB is left in, and the start takes it as after part 1. `newFile()`'s
  open does not run it.
* **The cut, at the first append** (after Codex's review, section 10;
  its recommendation (b)). The open changes no file. The first append
  with bytes, in `DbFile.append()` before its check of the file's
  length and its write, truncates the file where the run starts
  (`FileStreamIo.truncate()`, new, `setLength`) and forces it (a new
  `Force.ZERO_TAIL`), also with per-append forcing off; so does a cut
  that deletes files before the first append (`pretruncate()`, after
  Codex's second review); `close()` and an append of nothing do not. A failure of either is the stream's, and
  the next open leaves the zeros out again.
* **One case left alone.** A stream whose only file is all zeros: a
  repair never empties a stream, as an empty stream is a new database
  and `DatabaseBuilder.open()` must never create one (the start refuses
  it as before). On `028-60b` an encrypted stream was a second case,
  with the removal off (section 10); since 028-69 there is no encrypted
  stream, and the rule has no exception and no way to turn it off
  (section 11). Nothing above `FileStream` changed: `AppendOnlyStream`,
  `RecoverableStream` and `DatabaseBuilderImp` are unchanged.
* **Reporting.** `FileStream` has no log or listener; it reports by
  exceptions and its Javadoc. `getZeroTailRemoved()` (new) returns the
  number of bytes the open removed, 0 if none, for tests and tools.
* **What a start changes.** A start refused before it writes (another
  node size, an unsupported version, bytes that are not a BergDB
  stream's, a creation that did not complete) leaves the files as they were, the zeros too, so the
  refusals' "The start has written nothing" holds. A recovery may append
  before a later check refuses a start; then the cut is made: the first
  append is not proof that the start succeeded (Codex). A stream that
  ends in a recovery's zeros of an aborted record, with nothing written
  after, has them left out at each open and written again by the
  recovery: the same bytes.
* **Texts.** `FileStream`'s class Javadoc (a tail of zeros; the backup's
  one exception to appends only, and a copy that overlaps the cut),
  `zeroTailLength()`, `DbFile.cutZeroTail()`, `FileStreamIo.truncate()`
  and `Force.ZERO_TAIL`, `Database`'s "What a crash keeps"; 027-14,
  027-11 (1.3), 027-03 (section 6), 014-01 (a note at section 7),
  035-01 (section 12), 033 (RB-012), `releases/next.md`.
  `DatabaseBuilder.start()`'s Javadoc is as before part 2.
* **Not changed:** the C clone (item 012, following release 2026.2),
  whose file storage is its own; release 2026.6's notes (RB-012's
  bullet in "After the release" says "fixed in part").

### 9. Part 2, tests and runs

Tests (unit and f), on synthetic files:

* `FileStream.testZeroTailRemoved`: a stream of the bytes 7, 0, 0, 10,
  then 0, 1, 4,095 and 8,000,000 zero bytes left out, 8,000,001 left
  in; the stream's length, a read past its end and
  `getZeroTailRemoved()` checked; the file unchanged through an append
  of nothing, a close and a second open; the first append cuts it, and
  a third open has nothing to leave out.
* `FileStream.testZeroTailLastFileOnly`: a last file of zeros only left
  out whole and cut to 0 bytes at the first append, while the file
  before keeps its zeros; the only file all zeros left in. (On
  `028-60b` it also checked the removal off; gone with it, section 11.)
* `FileStream.testZeroTailCutAtFirstAppend`: with per-append forcing
  off, the forces are `OPEN`, then at the first append the truncation
  and `ZERO_TAIL`, then `CLOSE`; a truncation that fails fails the
  append and the stream, the file as it was.
* `FileStream.testZeroTailFileSize`: the last file's room for appends
  from its length without the zeros: 150,000 bytes and 100,000 zeros
  take 50,000 bytes more and a new file, not the 1 MB size of 250,000;
  200,000 bytes and 50,000 zeros are full, cut, and a new file follows.
* `FileStream.testZeroTailCutBeforeFirstAppend` (Codex's second
  review, its `LogicalProbe`): a first file of 200,000 bytes and a last
  one of 3,000 zeros (or 1,000 bytes and 2,000 zeros); a cut at
  200,000 before an append deletes the first file and cuts the zeros
  first, and the next open shows 200,000 (201,000), not 203,000; a cut
  that deletes nothing leaves the zeros. Fails on `af26333d`.
* `DbTesterStream.testRefusedStartsKeepZeroTail` (Codex's finding 4):
  starts refused for another node size and for meta block version 156,
  with 4,096 zeros after the stream, leave the file byte for byte; each
  starts with the size or version restored.
* `PubTester.testKeylessStartOfEncryptedFilesChangesNothing` (finding
  1, on `028-60b` only): an encrypted file database without
  `created.txt`, its last file ending in 3 zeros added by hand, refused
  without the key, its file byte for byte as before. It and
  `testRefusedStartsKeepZeroTail` failed on `5a25d1e0` (the truncation
  at the open). Replaced on `028-60c` (section 11).
* `DbTesterStream.testZeroedTailOverMetaBlock` (an f-test, 1.2 s),
  extended: zeros from inside the last record over two meta blocks
  (starts without that record, as in part 1); zeros from inside the
  record before it, over two records' starts, as seed 63 (refused in
  part 1, now starts with the records before, writes and starts again);
  0, 1 and 8,000,000 zero bytes after the last record's end (every
  record there, writes and starts again); 8,000,001 (left, refused "Bad
  transaction size in db stream, 0, spos P" at the last record's end).
* `PubTester.testFailedStartsDirectoryRemoved`: as before part 2, a
  creation cut at 200 bytes is refused (`DatabaseNotCreatedException`)
  and its file is 200 bytes (on `5a25d1e0` the open truncated it to 199).

The kept files (outside the repository, on copies, the branch's release
jar, a checker that starts each twice and compares its whole state with
KillWriter's oracle: every key, object, index scan both ways, counter):

* **Seed 63 starts**, with nothing done by hand, at k = 56,280, the last
  transaction a sync returned for, its state equal to the oracle's, twice.
  The open left the zeros from 3,915,776 to the end of
  `00000000093350.bergdb` out of the stream; the recovery's append cut
  them from the file, and the recovery completed the record at
  9,338,902,640 and aborted it (the file then 4,097,736 bytes, P less the
  file's first position, as cut by hand in part 1). The same after
  Codex's review (section 10), on a new copy of the kept files.
* **Seed 91 starts** at k = 122,334, its state equal to the oracle's,
  twice (as in part 1; the file 15,197,768 bytes after the recovery).
* 035-01's kept files (`z351/fs/*/keep/*.bin`, the probe's own bytes,
  not streams) are the two with a deleted file's bytes, not zeros:
  opened as a stream's only file, nothing is removed (028-67's case).

Gates (macOS, JDK 27, 2026-11-26, beside `week.sh` and other sessions'
runs). After Codex's second review (section 10), on the cut before
the first append and the backup text:

* `java/before-commit.sh`: BEFORE COMMIT OK (74 s; unit 1,762, f 90).
* `java/stress/kill-restart.sh 200`: SELF-CHECK OK, LATE EXIT OK, KILL
  RESTART OK: 200 kills and 8 exits in 285 s, seed 20261126.

After Codex's first review (section 10), on the change there:

* `java/before-commit.sh`: BEFORE COMMIT OK (76 s; unit 1,761, f 90).
* `java/stress/kill-restart.sh 200`: SELF-CHECK OK, LATE EXIT OK, KILL
  RESTART OK: 200 kills and 8 exits in 269 s, seed 20261126.
* 031-02's KillWriter, `-DnoSd=true`, on the branch's release jar: seed
  63, 250 kills, KILLWRITER OK (88,492 transactions, 552 older states),
  and seed 91, 250 kills, KILLWRITER OK (91,075 transactions, 548 older
  states); no zeroed tail of a kill came.
* The kept files, on new copies: seed 63 starts at k = 56,280 and seed
  91 at k = 122,334, each state equal to the oracle's, twice.

Before it, on `5a25d1e0`:

* `java/before-commit.sh`: BEFORE COMMIT OK (81 s; unit 1,758, f 90).
* `java/stress/kill-restart.sh 200`: SELF-CHECK OK, LATE EXIT OK, KILL
  RESTART OK: 200 kills and 8 exits in 295 s, seed 20261126.
* 031-02's KillWriter, `-DnoSd=true`, on the branch's release jar: seed
  63, 250 kills, KILLWRITER OK (82,295 transactions, 519 older states),
  and seed 91, 250 kills, KILLWRITER OK (76,174 transactions, 541 older
  states); fewer transactions than on 2026-11-25 under the machine's
  load. No zeroed tail of a kill came in these 500 kills; three starts
  found the last file ending in a recovery's zeros of an aborted record
  (KillWriter's note "a start's fill"), which the open removed and the
  recovery wrote again, every check passing.


### 10. Codex's review of part 2, and the change after it

Codex reviewed the branch at `5a25d1e0` (2026-11-26), with probes of
its own. The plaintext repair holds: the last complete record or valid
meta block ends in the byte 10, which stops the scan, so no synced
transaction is cut; a failed truncation or force fails the open, and a
halt after the truncation reopens. Its findings:

1. **A refused start without the key lost a synced encrypted
   transaction.** The opt-out follows the key given, not the stored
   bytes. Without `created.txt` (a copy of the `*.bergdb` files only), a
   start without the key opens the stream with the removal on; the open
   truncated a zero that ends a committed ciphertext record, and then
   the start was refused (bad magic bytes). Codex's `EncryptionProbe`:
   the file 36,088 bytes to 36,087, and the next start with the key read
   value-333, not the synced value-334.
2. **A minimum run length does not make the rule safe for encrypted
   streams.** A committed ciphertext record can end in a zero next to
   the system's zeros, and the runs merge: with 4,096 as the minimum,
   a synthetic tail of 035-01's page geometry cut a synced value
   (`MinimumDatabaseProbe`); given such a run, about 1 in 256.
3. **The backup paragraph.** A copy taken while a reopen repairs the
   tail can mix generations: zeros of the old file over a new record,
   with its new last byte 10 (`BackupProbe`; the start refused at the
   size 0).
4. **Refused starts changed the files.** Another node size and an
   unsupported meta block version were refused after the open had cut
   the zeros (`RecoveryProbe`: 4,512 bytes to 416), and their messages
   still said "The start has written nothing".

Done (2026-11-26, Codex's recommendation (b); the code in section 8):

* **The cut at the first append.** The open leaves the zeros out of the
  stream and changes no file; reads stop at the stream's end; the last
  file's size class is computed from its length without the zeros. The
  first append with bytes truncates the file and forces it
  (`Force.ZERO_TAIL`), also with per-append forcing off, before its
  check of the file's length and its write; not `close()`, not an
  append of nothing.
* **Findings 1 and 4, Codex's probes again**, on the branch's jar:
  `EncryptionProbe`, the start without the key refused, the file 36,088
  bytes before and after, and the start with the key read value-334, the
  synced value (the probe's own check, which expects the loss, now
  fails). `RecoveryProbe`: another node size refused, 4,512 bytes before
  and after; version 156 refused (`VersioningStreamException`), 4,512
  and 4,512; so "The start has written nothing" holds again. Its other
  cases as before. Unit tests: `testRefusedStartsKeepZeroTail` and
  `testKeylessStartOfEncryptedFilesChangesNothing` (section 9), which
  fail on `5a25d1e0`.
* **Finding 3.** `FileStream`'s class Javadoc and 027-14 now say: a copy
  of a stopped database is the database; a copy of a running one, in
  the order of the names, as before; except a copy that overlaps the
  first append after an open that left zeros out (after a kill, or of a
  copy that ended in zeros), which can hold the old file's zeros in
  place of bytes written after them and is not a backup. A running
  database is copied once it has committed a transaction since its
  start, which appends, or stopped (made precise after Codex's second
  review, below).
* **Finding 2: open, for Frans** on 2026-11-26; moot since 2026-11-27
  (section 11).

Codex's second review, of `af26333d` (2026-11-26): findings 1 and 4
fixed (its probes again: 36,088 bytes and the synced value-334 kept;
4,512 bytes kept by both refusals); the plaintext recovery and append
path holds, also with failed forces and writes at the cut and process
halts after the truncation. Two findings, fixed on the same branch:

* **A commit is not a barrier for a copy.** A commit can return with
  its bytes still in `BufferedStream`, before the first append and its
  cut (`BackupCommitProbe`: a copy begun after a commit holds the old
  zeros over the new record, refused at the size 0 at 536). The backup
  paragraph (`FileStream`, 027-14) now says: a copy begins after an
  append since the open has returned, or after `close()` has returned;
  for a running database, after a transaction that changed something,
  committed since the start, and a `sync()` that returned after it;
  for a stopped one, after its `close()` has returned (`stop()`
  returns before the close ends). `BackupCommitProbe` again: refused
  as before (a commit alone is not enough, as the text says); a copy
  of the probe that begins the copy after the commit's `sync()` starts,
  with the new value.
* **A cut before the first append brought the tail back.** A first
  file of 200,000 bytes and a last one of 3,000 zeros: the open showed
  200,000; `pretruncate(200000)` deleted the first file; the next open
  showed 203,000, the only file all zeros taken whole
  (`LogicalProbe`). Now a cut that deletes files cuts the pending zeros
  from the last file first, truncated and forced
  (`DbFile.cutZeroTailIfPending()`). `LogicalProbe` again: 200,000 ->
  200,000; its other cases as before. Unit test
  `testZeroTailCutBeforeFirstAppend` (section 9).

**The repair and encrypted streams** were an open question for Frans
on 2026-11-26: the opt-out above, a check inside `FileStream` whether
the stream is plaintext, or a repair at the record level above it.
Frans removed the internal crypto code instead (028-69, 2026-11-27);
section 11.


### 11. Without the opt-out, on 028-69 (2026-11-27)

Frans had the internal crypto code removed (028-69, `1809e04c` on
`main`): `SalsaStream`, `CryptoKey` and `DatabaseBuilderImp.cryptoKey()`
are gone, and no stream of BergDB is encrypted. The opt-out had nothing
left to protect. On the branch `028-60c`, the three commits of `028-60b`
on `main`'s `ae1b829b`, and then:

* **Removed with the opt-out:** `DatabaseBuilderImp`'s
  `openDir(dir, removeZeroTail)` (back to `new FileStream(dir)`, as on
  `main`); `FileStream`'s constructor
  `FileStream(dir, io, forceAppends, removeZeroTail)` and its field;
  the part of `testZeroTailLastFileOnly` with the removal off;
  `PubTester.testKeylessStartOfEncryptedFilesChangesNothing` (it needs
  the crypto key); the Javadoc and 027-14's sentence on encrypted
  streams. The repair is a rule of `FileStream` alone, for every
  stream, with no way to turn it off; `FileStream`'s Javadoc says so,
  and that a stream of other bytes than BergDB's format would lose its
  trailing zeros at an open that appends.
* **In its place:** `PubTester.testEncryptedByAnEarlierReleaseRefused`
  (028-69's test of a database that 2026.3 encrypted, its stream's bits
  flipped) starts without `created.txt` also with 3 zeros after the
  last file's end: refused by the magic bytes before anything is
  appended, every file byte for byte as before; finding 1 in the form
  that is left. With the cut at the open (a mutation), it fails.
* **Codex's findings again.** Moot, as they concerned only encryption:
  finding 2 of the first review (a minimum run length is not safe for
  ciphertext), the encrypted part of finding 1 (a ciphertext zero at
  the end of a committed record), and the second review's view of the
  three alternatives. Fixed, and still fixed on `028-60c`, each by its
  test or probe: findings 1 and 4 of the first review (refused starts
  change no file): `testRefusedStartsKeepZeroTail` and the test above
  pass, and fail with the cut moved to the open; Codex's
  `RecoveryProbe` again: another node size and version 156 refused,
  4,512 bytes before and after. Finding 2 of the second review (a cut
  before the first append): `testZeroTailCutBeforeFirstAppend` passes,
  and fails without the cut in `pretruncate()`; `LogicalProbe` again:
  200,000 -> 200,000. Finding 3 of the first review and finding 1 of
  the second (the backup paragraph): the text in `FileStream` and
  027-14 as on `028-60b`. Codex's `MetaProbe` and `CrashProbe` pass as
  before.

Gates on `028-60c` (macOS, JDK 27, 2026-11-27, beside other sessions'
runs):

* `java/before-commit.sh`: BEFORE COMMIT OK (66 s; unit 1,726, f 90),
  and after Codex's review below, BEFORE COMMIT OK (64 s; unit 1,726,
  f 90).
* `java/stress/kill-restart.sh 200`: SELF-CHECK OK, LATE EXIT OK, KILL
  RESTART OK: 200 kills and 9 exits in 248 s, seed 20261127.
* 031-02's KillWriter, `-DnoSd=true`, on the branch's release jar: seed
  63, 250 kills, KILLWRITER OK (110,368 transactions, 532 older states),
  and seed 91, 250 kills, KILLWRITER OK (123,449 transactions, 545 older
  states); no zeroed tail of a kill came.
* The kept files, on new copies of 031-02's, the branch's release jar,
  KillWriter's oracle checked twice: seed 63 starts at k = 56,280 (the
  last file cut from 4,374,528 to 4,097,736 bytes) and seed 91 at k =
  122,334, with nothing done by hand.

Codex's third review (2026-11-27), of `main...028-60c` and of 028-69's
`1809e04c`, with probes of its own: the repair and the removal hold; no
loss of a committed or synced transaction within the storage's fault
model; every writer's records and valid meta blocks end in 10 (fills of
recovery, maintenance and reclaim are inside records; no
preallocation), and the trailing zeros of an aborted record or a cut
meta block are left out and written again by the next recovery
(five cycles). A database that release 2026.3 encrypted with its real
key (built from the tag) is refused, with and without `created.txt`,
and with 3 zeros after its last file, every file unchanged. No dead
reference to the removed code. Two findings:

* **The backup barrier needs an append of at least one byte**: an
  append of nothing returns without cutting the zeros, and a copy begun
  after it can still mix the old zeros with a new record (its
  `ReviewProbe`). Fixed in the text: `FileStream`'s class Javadoc and
  027-14 say "an append of at least one byte since the open"; the
  behaviour, that an append of nothing does not cut, is
  `testZeroTailRemoved`'s.
* **A start refused after its recovery has written** (a committed
  record of a format version this release does not read, refused by
  `VersioningStreamException` after `RecoverableStream.recover()`
  completed a torn last record): the start appends, and on this branch
  the pending zeros are cut first. The same refusal changes the stream
  on `main` (Codex ran both); the message does not say that nothing was
  written, and `FileStream`'s Javadoc and 027-14 say that a recovery may
  append before a later check refuses a start. Not changed here: a
  check of the records' versions before the recovery writes is a
  change of the start's order, outside this entry.


Log
---

2026-11-25. Registered by lead-1125, from 031-02's finding F1.

2026-11-25. Taken by an agent of lead-1125. Part 1 made and gated on the
branch `028-60`: a meta block of zeros is not valid, and a cut block of
zeros is completed with zeros (section 3); seed 91's files start, seed
63's are refused as documented and start when cut at P. Part 2, zeros
past a record's end, written as options B1 to B3 for Frans (section 4;
recommended: B2).

2026-11-25. Codex's review of part 1 (lead-1125): the fix holds for the
fault; two texts corrected: the refusal may append a cut meta block's
missing bytes (recover() completes it before it reads the sizes), and a
size field cut by the end (1 to 3 zero bytes) is recovered as a torn
record's; Codex favours B2 for part 2, with every byte from P to the
end checked to be zero, the cut forced, and repeated crashes during the
repair tested; B1 acceptable for a release meanwhile.

2026-11-26. Part 2 waits for 035-01's first results (Frans): the cause
of the zeros on macOS, and whether other systems leave them.

2026-11-26. 035-01's results (sections 4 to 11): zeros after a kill on
APFS only (s1's ext4 left clean prefixes); B2 with four conditions
recommended (zeros from the 4 KiB boundary at or before P, the last
file's length a multiple of 4,096, P in the last file, a run of at most
8 MB); a new risk: on APFS disk images and RAM disks a cut write held a
deleted file's bytes, not zeros, which no option covers (035-01).

2026-11-26. Part 2 decided by Frans (section 7: neither B1, B2 nor B3 as
written; the repair in `FileStream` only, the same on every system) and
done by an agent of lead-1126 on the branch `028-60b`: `FileStream`'s
open removes a run of zero bytes of at most 8 MB at the end of its last
file (section 8); seed 63's kept files start at k = 56,280, the last
synced, with nothing done by hand; tests and gates in section 9. Off for
an encrypted stream, and a stream whose only file is all zeros is left
(section 8). Status done.

2026-11-26. Codex's review of part 2 (lead-1126; section 10): the
plaintext repair holds; four findings: a refused start without the key
of an encrypted database cut a synced transaction's last byte; a
minimum run length does not make the rule safe for encrypted streams;
a copy that overlaps the repair can mix generations; refused starts
changed the files while their messages said "written nothing". Done by
an agent of lead-1126 on the branch `028-60b`, as Codex's
recommendation (b): the open leaves the zeros out of the stream and
changes no file, and the first append cuts and forces them; findings 1
and 4 fixed (Codex's probes again, two new unit tests); the backup
paragraph corrected; finding 2 open for Frans, the internal-key opt-out
kept. Gates in section 9.

2026-11-26. Codex's second review, of `af26333d` (lead-1126; section
10): findings 1 and 4 fixed, the plaintext path holds; two findings,
fixed by an agent of lead-1126 on the branch `028-60b`: the backup
paragraph names the barrier for a copy (an append returned since the
open: for a database a changing transaction and a `sync()` after it,
or a returned `close()`), and a cut that deletes files before the first
append cuts the pending zeros first, so a last file of zeros only is
not taken whole at the next open. Probes again and gates in sections 9
and 10.

2026-11-27. Frans decided to remove the internal crypto code (028-69).
Part 2's choice for encrypted streams (section 10 on the branch
`028-60b`) falls away with it: the branch is rebased on 028-69 without
its opt-out, looked at by Codex again, and landed.

2026-11-27. Rebased by an agent of lead-1127 on 028-69 without the
opt-out for encrypted streams, on the branch `028-60c` (section 11):
the repair is a rule of `FileStream` alone, for every stream; Codex's
findings that concerned only encryption are moot, the others still
fixed by their tests; gates in section 11. Codex's third review: the
repair and the removal hold; the backup barrier is an append of at
least one byte (text fixed); a start refused after its recovery has
written is as on `main`, not changed. Status done.
