028-60. Fix: after a kill, a zeroed tail over a meta block stops the start
=========================================================================

Status: open: part 1 done (a meta block of zeros is not valid; the branch
`028-60`), part 2 for Frans's decision. Kind: Fix. Frans: decision (part
2, section 4).
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
  length: L." and writes nothing; a person keeps a copy, cuts the file
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


Log
---

2026-11-25. Registered by lead-1125, from 031-02's finding F1.

2026-11-25. Taken by an agent of lead-1125. Part 1 made and gated on the
branch `028-60`: a meta block of zeros is not valid, and a cut block of
zeros is completed with zeros (section 3); seed 91's files start, seed
63's are refused as documented and start when cut at P. Part 2, zeros
past a record's end, written as options B1 to B3 for Frans (section 4;
recommended: B2).
