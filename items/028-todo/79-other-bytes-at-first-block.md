028-79. Fix: other bytes at a meta block's position, once taken, refuse a later start
=====================================================================================

Status: done (2026-11-28): fix (1) and the review's two shapes on
`main` (`2d4d178a`, `b9624ea1`, `01232710`); E, the second review's
residual (`a40a39c6`); (F) and (G), found with it (`6ef2c7dd`,
`3560f331`).
Kind: Fix. Frans: none; the smaller fix went ahead by default at 10:30
on 2026-11-28.
Created 2026-11-28 by Frans Lundberg.

What: another file's bytes at a stream file's first meta block can be
taken by a start, inside an aborted record or by the documented cut at
P, and stay in the stream. When reclaim's cut later makes that file the
stream's first, the next start refuses a database that ran and stopped
cleanly since, with a message that names no way out. Severity S2 (033's
rules), on a storage that can leave a deleted file's bytes at the start
of a new file. The review of the start path of 2026-11-28 (033,
`reviews/2026-11-28-start.md`, F2) showed it by probes
(`StaleFirstBlockProbe`, six variants; `StartChain` with other bytes met
it in 9 of 400 chains).

Its reach: 028-67's rule is for other bytes from any page boundary of
the last file, and a new file's start is one. 035-02's kills left other
bytes only from 2 MiB into a cut first write of a new file, and zeros
before that, so on the devices measured there a file's first block was
not reached. It is a gap in the rule as the code and 027-03 state it,
not a case seen on APFS. No release has C3's rule of the first block
(not a released bug).

How other bytes get to the block's position, with a start that takes the
stream:

* **Inside a record that the start aborts.** A kill cuts the first write
  of a new stream file, and the file holds other bytes from its start.
  The record that reaches over the file's first block has its header in
  the file before; the header holds its check, so the walk takes the
  record as cut and completes it (`tornRecordIsOwn`). Its content is not
  read, and the other bytes at the block's position stay, inside an
  aborted record. Every start passes over the block
  (`readOwnMetaBlock`).
* **By the way out of a `BadTailException`.** Where the last record
  before the other bytes ends exactly at the block's position, the walk
  refuses the tail with P 128 bytes after the block (`walkTail`,
  `verified = next`: the position steps over the block). The stream cut
  at P as the message says keeps the other bytes at the block's
  position, and the start takes it.

Then the cut makes the file the stream's first, and
`RecoverableStream.readFirstMetaBlock` meets the block: it throws for a
block without the magic bytes and this version, and takes the first
block whose last byte is 10 as the stream's first. 028-76's fix passes
over recovery's fill and a block of zeros; a block of other bytes is
neither. The four refusals, by what the bytes are: "Invalid magic bytes
in stream" (not a block); "Could not find *any* valid meta block ... it
may lack bytes that the database needs" (an older stream file's block of
this database); "The meta block at 800000 names the last transaction at
797296, before the stream's first position" (another database's block
at the same position, whose ID the start takes); "Cannot read meta block
with version 155" (a block of 2026.6). `leftoverProblem` refuses the
same block as the first of a file before a gap, with 028-66's way out.

Why: nothing is written by the refused start and no record is lost, but
the database does not start, no message says what to do, and two of the
messages say that bytes are missing, which they are not. 027-03,
section 6, argues that "the first block is the stream's own: a stream's
bytes are cut only from its end, and a kill's other bytes are in the
last file"; that holds at the start after the kill, and the last file
of that start is the first file of a later one.

The two fixes that the review names:

* **(1) The walk of the tail refuses other bytes at a meta position
  inside the tail that it takes.** The walk checks the blocks at the
  meta positions of a cut record that it would complete, and the block
  after the last whole record, as its own (valid and holding their
  position and the ID, or a completion's block that is not valid, or
  zeros, or cut by the stream's end), and refuses any other bytes there
  with a `BadTailException` whose P is before the record, or at the
  block's position where a whole record ends there, not 128 after it.
  The cut at P then leaves no other bytes at a meta position, so no
  later first block can be one. 028-76's rule and
  `readFirstMetaBlock` stay as they are. The cost: a start refuses, with
  the cause and P, a tail that it takes today (the record cut over a
  block of other bytes), and a person cuts it, as for the other tails of
  other bytes. The smaller change.
* **(2) Every reader of a first block passes over what is not this
  database's.** `readFirstMetaBlock` and `leftoverProblem` pass over a
  block that fails any check (the magic bytes, the version, the
  position, the ID), not only one that is not valid by its last byte.
  For that the database's ID must come from a source that other bytes
  cannot give: today it is read from the first valid block, which
  another database's block at the same position can be. It also needs a
  rule for a stream of another version or another database as a whole
  (the refusal of a 2026.6 database rests on its first block's
  version). A wider change of which blocks may lie in a stream, a
  question of the storage model (028-77).

Decided by the lead (class 2, 2026-11-28): (1) goes ahead by default at
10:30 on 2026-11-28 unless Frans says otherwise; (2) is left to 028-77.

Done when: `StaleFirstBlockProbe`'s six variants and `StartChain` with
other bytes give no refusal other than a `BadTailException` with a P
whose cut starts with every committed record (and 028-76's decided case
(a)); tests that fail before the fix, on `MemoryStream` and on files;
027-03, section 6, and 027-11 state the rule; `java/before-commit.sh`
prints `BEFORE COMMIT OK`; `level3.sh`, 031-06's sweep and faults, the
power-loss tester and `DbTesterTail` pass.

First step: the review's F2 and `StaleFirstBlockProbe`; `walkTail` and
`tornRecordIsOwn` in `RecoverableStream`.

Found by: the review of the start and recovery path of 2026-11-28 (033,
`reviews/2026-11-28-start.md`, F2).


Result
------

Fix (1), on the branch `start-fixes`, after 028-80, on 028-70's branch
(2026-11-28). Fix (2) is not built (028-77).

* **The rule.** `RecoverableStream.walkTail` reads the meta blocks after
  the last valid block B where it does not read a record's content: in
  the record that the end of the stream cuts, in an aborted record, and
  the block right after a whole record that ends at its position. Each
  must hold, as far as the stream holds it, zeros or the begin of the
  block that the database writes there followed by zeros: B's bytes but
  the last transaction's position (offsets 16 to 23, any) and the
  block's own position at 46 (`foreignBlock`). So recovery's fill, its
  completion of a cut block, a block that a kill cut and a block of
  zeros pass; random bytes, an older stream file's block of the
  database, another database's block and a block of version 155 are
  refused with a `BadTailException`, before anything is written: in a
  record, with P its start (the end of the last record that is one); after a whole record
  that ends at the block, with P the block's position, no longer 128
  bytes after it. A block inside a whole committed record is not read:
  its content is the database's, parsed where another file's bytes can
  begin in it (`DbTesterTail.testOtherBlocksPassedOver`, a block of
  another place or ID inside committed records, still starts). The
  walk's other refusals come first, so a committed record of another
  format is still a `VersioningStreamException` (028-70).
* **Why the aborted record too.** The fix as registered names the cut
  record and the block after the last whole record. An aborted record
  is the third place where the walk passes over a block unread: a kill's
  other bytes that begin after a record's header and put a 0 at its
  last byte make it a whole aborted record, which the walk counts, and
  the refusal of the bytes after it gave a P after the record, so the
  cut at P kept the record and its block. Every aborted record that a
  database writes is recovery's completion: zeros and blocks of its own.
* **What it settles.** No start takes a stream that holds other bytes
  at a meta block's position after its last valid block, so no later cut
  can make such bytes a stream file's first block, and the four
  refusals of the review's F2 do not come. 028-76's rule and
  `readFirstMetaBlock` are unchanged. Not settled: a copy of the
  database at the same positions (028-78, F1), whose blocks pass every
  check.
* **The cost**, the tails that a start took and refuses: a record that
  the end of the stream cuts, whose header holds its check, with other
  bytes at a meta block's position after its header; an aborted record
  over such a block; a stream that ends at or inside a block of other
  bytes after a whole record that ends at the block (taken before, the
  block completed with the fill). Each is refused with P before the
  record, or at the block, and starts after the cut at P with what the
  stream held at the kill: the cut record was not committed. A person
  cuts the stream, as for the other tails of other bytes. Tails refused
  before with P 128 bytes after the block are refused with P at it.
  The counts of the review's `StartChain` with other bytes: the gates
  below.
* 027-11, 1.3 and section 7, and 027-03, sections 6 and 7, state the
  rule.

Tests, each failing before the fix and passing after it (2026-11-28):

* `RecoverableStream.testForeignBlockRefused` (`MemoryStream`): a meta
  block at 400,000 of random bytes, of another place, of another
  database, of version 155, of zeros, the fill, and a block cut after 60
  bytes and completed, in a record that the end of the stream cuts, in
  an aborted record, and after a record that ends at the block with 300
  and with 50 bytes of the stream from it. The first four are refused,
  P the record's start or the block's position, the stream unchanged;
  the last three are taken (with 300 bytes, the random bytes after the
  block refused at P 128 after it). Before: "random bytes, in a cut
  record: P, expected 380256, got -1" (taken).
* `FileStreamPowerLossTester.testOtherBytesAtAFilesFirstBlockRefused`
  (f): 028-76's file test with the file at the kill's block holding 300
  other bytes (random bytes, the first file's block, another
  database's): the start refuses with P the start of the record over the
  block and changes no file; cut at P it starts with every key, and
  again after reclaim's cut has made the block's file the first. Before:
  "random bytes: P, the record over the block, expected 787736, got -1"
  (taken; the start after the cut refused, as in the review).

The review's `StaleFirstBlockProbe` on the branch (2026-11-28): `none`
start 2 ok; `random`, `older`, `other`, `v155` refused at start 1 with
P 787736, the start of the record over the block at 800000, cut there,
start 1 ok, start 2 ok with every key; `random exact`, `older exact`,
`other exact`, `v155 exact` refused at start 1 with P 400000, the block,
cut there, start 1 ok, start 2 ok with every key. `sameid` and `sameid
exact` are F1's (028-78): the copy's block is taken as the last valid
block, as before; `sameid exact` still loses committed records by the
cut at P.

Gates of the first build (2026-11-28, on F53 beside other sessions'
runs, on 028-80 and 028-70's follow-up): `BEFORE COMMIT OK (159 s)`;
`StartChain 70000 70099 20 2 30 1 0`, 2,000 starts, 25 of 028-76's
decided case, no failure; `StartChain 60000 60099 20 2 30 1 25`, 2,000
starts, of 176 tails of other bytes 105 refused with P and started
after the cut, 63 taken, 28 of the decided case, no failure and no later
refusal of F2; the night tests of `DbTesterTail` and
`CorruptStreamTester`, SUCCESS, 5 tests; `PowerLossTest 1001 12 3000 3`,
POWERLOSS OK; 031-06's `faults.sh` bad 0 in each of 42 lines and
`sweep.sh` 0 different in each of 63; `LEVEL 3 OK`; `KILL RESTART OK:
1000 kills and 50 exits in 1364 s, seed 20261128`.


Review
------

Reviewed on 2026-11-28 by a second agent of lead-1127, independent of
the change: no S1. It checked that no sound file stream is refused,
that P is always right, that the aborted record as a third place is
right and needed, and that the bytes are the parent's in 12,520 cases
of its `SameBytesProbe` but for the case (B) below. Two shapes of a
block's first 8 bytes, the magic and the version, fixed on the branch:

* **(A)** S2 where F2 applies, rare, not a regression. A block of the
  database's first 1 to 4 bytes and zeros, with other bytes after it in
  the record that the end of the stream cuts, as a kill 1 to 4 bytes
  into a file and other bytes from there leave it, was taken as a block
  that a kill cut. Recovery never leaves such a block with bytes after
  it: its fill writes the magic bytes and the version first. Once
  reclaim's cut made the file the first, a start refused with F2's
  messages (`BadMagicBytes`, or "Cannot read meta block with version
  0"). `StartChain` met it once (seed 60016); the review's
  `OwnPrefixProbe` shows it for 1 to 4 bytes. Fixed: such a block is the
  database's only where the stream ends in it, where the record's bytes
  after it are zeros, to the record's end, the stream's or the next meta
  block, as a completion writes them, or right after a whole record;
  and a refusal right after a block that a later start could not read
  as its first (`readFirstMetaBlock`: zeros, or the magic bytes and the
  version) has P at the block, so that the cut at P leaves none.
* **(B)** S4, a regression, on `MemoryStream` only. A kill's zeros
  (028-60) that end 2 to 4 bytes into a block after 1 to 3 of its bytes:
  the start takes the stream and completes the block with the fill from
  the stream's end, which writes the rest of the magic bytes and the
  version after the zeros, and the next start refused that completion,
  "does not begin as a meta block", after every kill inside it too.
  `FileStream`'s open leaves such zeros out, so a file database was not
  affected. Fixed: the database's first bytes, a run of zeros and the
  template's bytes from the run's end pass.
* Test: `RecoverableStream.testFirstBytesOfABlock`, failing before ("1
  bytes and zeros, other bytes after it in a cut record: P, expected
  380256, got -1"): (A) in a cut record with other bytes and with zeros
  after the block, and after a whole record; (B) at 1 to 3 bytes with
  zeros to 2 to 4, in a record and after one, taken at the second start.

Gates after the review's fix (2026-11-28, on F53 beside other sessions'
runs, on `main` with 028-80, 028-81 and 028-82):

* `java/before-commit.sh`: BEFORE COMMIT OK (141 s).
* The review's probes: `OwnPrefixProbe`, the block of 1 to 4 of the
  database's bytes and zeros with other bytes after it refused at start
  1, with P the record's start, and no later start refused (k of 0, a
  block of zeros, is note (C)); `CutBlockZerosProbe`, start 2 ok in all
  20 cases; `SameBytesProbe 12520`, the parent's bytes wherever both
  start, and 8 lines differing, each refused by both: a block of the
  database's first 1 to 4 bytes and zeros after a record that ends at
  it, with zeros past it, now with P at the block, 400000, not 400128.
* 033's probes: `CreationZerosProbe`, 25 `DatabaseNotCreatedException`;
  `StaleFirstBlockProbe`, start 2 ok in every variant but `sameid exact`
  (F1, 028-78); `StartChain 70000 70099 20 2 30 1 0`, 2,000 starts, 22
  of 028-76's decided case, no failure; `StartChain 60000 60099 20 2 30
  1 25`, 2,000 starts, of 174 tails of other bytes 101 refused with P and
  started after the cut, 69 taken, 37 of the decided case, no failure
  and no later refusal of F2.
* `PowerLossTest 1001 12 3000 3`: POWERLOSS OK, 12 seeds, 732 cold
  recoveries, without per-append forces 744; negative controls caught.
* 031-06's probes: `faults.sh`, bad 0 in each of its 42 lines;
  `sweep.sh`, 0 different in each of its 63 lines.
* `java/stress/level3.sh`: LEVEL 3 OK.

Notes of the review, not fixed:

* **(C)** S3, not a regression. A block of zeros at a file's first
  position, followed by other bytes, passes as zeros. After a power loss
  in a cut's batch the file lies before a gap, and `leftoverProblem`
  refuses it with 028-66's way out: a sibling of 028-76's decided case
  (a). `StartChain` met it in seeds 60104, 62116 and 63022 (60104 on the
  parent too).
* **(D)** By reading. A foreign block inside the last committed record,
  whose nodes end before the block, with only its padding and last byte
  after it (the record's last byte 10 among the other bytes), is still
  taken. And a stream of version 156 with such a block that a build
  before the fix took is now refused with P before later records; no
  release has version 156.

The second review, of the fix of (A) and (B) (2026-11-28, by the same
agent of lead-1127): land as it is. `OwnPrefixProbe` refused at the
record's start; `CutBlockZerosProbe` 20 of 20 shapes start twice;
`SameBytesProbe`, 12,520 cases, the bytes after each start identical
with the parent's wherever both start (8 lines, refused by both, with P
400000 instead of 400128); `StartChain` 3,000 starts plain, 1,000 with
`-Dforce=off` and 6,000 with other bytes, no failure (C twice). P at
the block moves only the P of a start that is refused anyway, to the
block after the record before it. One residual, fixed on 2026-11-28
(below):

* **(E)** S4, a residual of (A). `rawZeros` reads the zeros after a
  block of the database's first 1 to 4 bytes only up to the next meta
  block: such a block followed by zeros past the next block and then
  other bytes is still taken, and a later start from that block is
  refused (BadMagicBytes, or VersioningStreamException for 4 bytes).
  The review's `LongZerosProbe` shows it with zeros to 204,096 bytes
  past the block; with zeros to 4,096 bytes the same shapes are refused.
  It needs a kill 1 to 4 bytes into a block followed by at least about
  200 kB of zeros. The fix: the zeros read to the record's or the
  stream's end, passing over block positions.
* **E fixed** (2026-11-28, by an agent of lead-1127, on the branch
  `028-79-e`): the zeros after such a block are read to the end of the
  record that holds it, or to the stream's end for the record that the
  end cuts, the meta blocks among them passed over, as the walk reads
  each of them on its own (`RecoverableStream.zerosAfterBlock`, in
  place of `rawZeros`). A range found zero is kept for the walk, so that
  a later block of the record reads nothing again: the check reads each
  byte after the last valid block at most once, not a whole record.
* Test: `RecoverableStream.testFirstBytesOfABlockZerosPastTheNextBlock`,
  failing before ("1 bytes and zeros, zeros after it past the next
  block, then other bytes, in a cut record: P, expected 380256, got
  -1", and so in an aborted record): 1 to 4 bytes and zeros, zeros past
  the next block and then other bytes, in a cut record and in an aborted
  record, refused with P the record's start, the stream unchanged, and
  started after the cut at P; with zeros to the end of the stream or of
  the record, the next block zeros or the database's own cut after 60
  bytes, taken.

Probes and gates after E's fix (2026-11-28, on F53 beside other
sessions' runs, on `main` with 028-83 and 028-84; `java/before-commit.sh`
again with 028-85):

* `java/before-commit.sh`: BEFORE COMMIT OK (82 s); with 028-85,
  BEFORE COMMIT OK (74 s).
* The review's probes, against `main`'s build before the fix (01232710):
  `LongZerosProbe`, the block of 1 to 4 of the database's bytes and
  zeros with zeros to 4,096 and to 204,096 bytes after it and other
  bytes after them, refused at start 1 in all 8 cases with P the
  record's start, 980640 (before, the 4 with 204,096 were taken); with
  zeros to 404,096 too, and, cut at P and started, records appended past
  three more blocks and the stream cut at the block's position, a later
  start from there started in every case; `OwnPrefixProbe` and
  `CutBlockZerosProbe`, the same lines as `main`'s; `SameBytesProbe
  12520`, the same 12,520 lines as `main`'s.
* 033's probes: `StartChain 70000 70099 20 2 30 1 0`, 2,000 starts, 23
  of 028-76's decided case, no failure; `StartChain 60000 60099 20 2 30
  1 25`, 2,000 starts, of 187 tails of other bytes 103 refused with P
  and started after the cut, 75 taken, 24 of the decided case, no
  failure and no later refusal of F2. A run of both before the rebase
  onto 028-83, with the same `RecoverableStream`, had no failure either,
  and one later refusal in the second, note (C)'s (seed 60009: a new
  file's first block left zeros, other bytes after it, then a file
  before a gap).
* The night tests of `DbTesterTail` and `CorruptStreamTester`: SUCCESS,
  5 tests.
* `PowerLossTest 1001 12 3000 3`: POWERLOSS OK, 12 seeds, 732 cold
  recoveries, without per-append forces 744; negative controls caught.
* 031-06's probes: `faults.sh`, bad 0 in each of its 42 lines;
  `sweep.sh`, 0 different in each of its 63 lines.
* `java/stress/level3.sh`: LEVEL 3 OK.

Found with E's fix (2026-11-28; on `main` before E's fix as after it),
fixed on 2026-11-28 (below):

* **(F)** (A)'s block in a whole aborted record, with zeros after it
  past the record's end and other bytes after them, is refused with P
  at the end of the aborted record, after the block: the cut at P keeps
  the block, and a later start from it refuses the stream
  (`BadMagicBytes`, or a `VersioningStreamException` for 4 bytes). It
  needs fewer zeros than E, to past the record's end. Shown on
  `MemoryStream`: a record of 21,000 or 50,000 bytes over the block at
  1,000,000, the block's first 1 to 4 bytes and zeros to 3,000 bytes
  after the record's end, then 9,000 random bytes.
* **(G)** (A)'s block in the record that the end of the stream cuts,
  with zeros only after it to the stream's end, is taken, as the rule
  says, and stays: a later start from it refuses the stream in the same
  way. Shown on `MemoryStream`, which keeps such zeros; `FileStream`'s
  open leaves a run of zeros of up to 8 MB at the end of the last file
  out of the stream (not tried there).
* (B)'s block, the fill's completion of a block cut after zeros, which
  the walk takes since the first review, refuses a later start from it
  in the same way (`BadMagicBytes`), on `MemoryStream`: 6 of 6 shapes,
  1 to 3 bytes with zeros to 2 to 4, in a record that the end cuts.

**F and G fixed** (2026-11-28, by an agent of lead-1127, on the branch
`028-79-fg`, as the lead decided: the root of both, not the walk's P):
`RecoverableStream.readFirstMetaBlock` passes over a block whose every
byte is the fill's at its offset or 0 (`fillOrZeros`), as it passes over
the fill and a block of zeros since 2026-11-28 (week.sh's apps-kill-cc),
and takes the first valid block after it; so does its read of the first
8 bytes of a stream shorter than its first block. The blocks it passes
over now: zeros, the fill, (A)'s block and (B)'s; any other bytes of the
magic and the version are refused as before, among them a block of
2026.6 (version 155) and another version's. Why it is sound:

* **A start needs nothing in such a block.** It holds at most the magic
  bytes and the version, and zeros: no position, no database ID, no last
  transaction, no time; and it is not valid (its last byte 0). The fill,
  passed over before, holds the same. Of the first block a start takes
  its ID and its own position only, and the block taken is still the
  first valid one, which must hold its own position (`isOwn`); its ID is
  the stream's, compared with `created.txt`'s (028-81) as before.
* **No stream that a cut made begin inside a record is taken for it.**
  The blocks after the first are read as before (`readOwnMetaBlock`
  passes over every block that is not this database's valid one), and
  the last valid block must name a record at or after the first position
  (`checkLastTransSpos`), else the start refuses, "names the last
  transaction at ..., before the stream's first position": with such a
  block first as with the fill first. A probe that cut a stream at such
  a block inside an aborted record that the last block still named met
  that refusal, as it should.
* **A file before a gap whose first block is such a block is refused as
  before**: `leftoverProblem` is unchanged ("does not begin as a meta
  block", or "is of version 0"), with 028-66's way out, as for the fill
  (028-76's decided case (a)).
* **F needs no change of the walk's P**: the cut at P keeps the block,
  and the start after reclaim's cut that makes its file the first passes
  over it. The walk's rule (A) is unchanged: such a block followed by
  other bytes in a record is refused, as it is no completion of the
  database's; P at a block after the last valid one that is not zeros
  or the magic and the version (`readableAsFirst`, badTail()) is kept,
  so that a cut at P leaves no such block for a file before a gap.
* On `FileStream`, F and G need a run of zeros of more than 8 MB: the
  open leaves a shorter one at the end of the last file out, and the
  start then completes the block as the fill, which a later start passes
  over. (B) needs zeros that the storage keeps.

Tests, each failing before (2026-11-28):

* `RecoverableStream.testFirstBlockOfTheFillsBytesPassedOver`
  (`MemoryStream`): (F) for 1 to 4 bytes, refused with P at the aborted
  record's end, cut at P; (G) for 1 to 4 bytes, taken; (B) for its 6
  shapes, taken; each then started with records past three more blocks
  and cut at the block's position, as reclaim's cut leaves it: it
  starts, its first block the next one; and (F)'s block as a piece
  before a gap, refused by `leftoverProblem`. Before: "F, 1 bytes and
  zeros past the aborted record's end: the start after the cut at
  1000000: bergdb.storage.BadMagicBytes: Expected magic bytes: 62657267,
  got: 62000000".
* `FileStreamPowerLossTester.testFirstFileBeginsWithTheFillsBytes` (f):
  a file database after reclaim's cut, its first file's first block
  written over with the database's first byte and zeros, its first 4
  bytes and zeros, and the fill after zeros (2 bytes, 2 zeros, the
  template): it starts, and every key reads as before. Before: "the
  first byte and zeros: the start refused: ... Invalid magic bytes in
  stream".

Probes and gates after the fix of F and G (2026-11-28, on F53 beside
other sessions' runs, on `main` with E):

* `java/before-commit.sh`: BEFORE COMMIT OK (99 s).
* The review's probes, against `main`'s build with E: `SameBytesProbe
  12520`, the same 12,520 lines; `LongZerosProbe`, `OwnPrefixProbe` and
  `CutBlockZerosProbe`, the same lines. The probes of F, G and (B):
  each later start from the block, refused on `main` in 8, 12 and 6
  cases, starts.
* 033's probes: `CreationZerosProbe`, 25 `DatabaseNotCreatedException`,
  as on `main`; `StaleFirstBlockProbe`, start 2 ok in every variant but
  `sameid exact` (F1, 028-78); `StartChain 70000 70099 20 2 30 1 0`,
  2,000 starts, 22 of 028-76's decided case, no failure; `StartChain
  60000 60099 20 2 30 1 25`, 2,000 starts, of 185 tails of other bytes
  103 refused with P and started after the cut, 72 taken, 33 of the
  decided case, no failure and no later refusal of F2.
* The night tests of `DbTesterTail` and `CorruptStreamTester`: SUCCESS,
  5 tests.
* `PowerLossTest 1001 12 3000 3`: POWERLOSS OK, 12 seeds, 732 cold
  recoveries, without per-append forces 744; negative controls caught.
* 031-06's probes: `faults.sh`, bad 0 in each of its 42 lines;
  `sweep.sh`, 0 different in each of its 63 lines.
* `java/stress/level3.sh`: LEVEL 3 OK.


Log
---

2026-11-28. Registered by lead-1127 from the review's F2; an agent of
lead-1127 prepares fix (1) on a branch; it lands by default after 10:30.

2026-11-28. Fix (1) built on the branch `start-fixes` by an agent of
lead-1127, after 028-80, with the aborted record as a third place.

2026-11-28. Reviewed by a second agent of lead-1127; its shapes (A) and
(B) fixed on the branch, its notes (C) and (D) recorded (Review).

2026-11-28. The gates after the review's fix passed (Review).

2026-11-28. Fix (1) and the review's two shapes on `main`
(`2d4d178a`, `b9624ea1`, `01232710`), gated on the combined tree:
BEFORE COMMIT OK (138 s), LEVEL 3 OK. The second review's residual (E)
open, its fix in work by an agent of lead-1127 (branch `028-79-e`).

2026-11-28. The second review's E fixed by an agent of lead-1127 on the
branch `028-79-e`; the gates passed; (F) and (G) found (Review).

2026-11-28. (F) and (G) fixed by an agent of lead-1127 on the branch
`028-79-fg`: a first block whose every byte is the fill's or 0 is passed
over; the gates passed (Review).

2026-11-28. Done: E (`a40a39c6`), (F) and (G) (`6ef2c7dd`, `3560f331`)
on `main`. The second review of the start path on `main` at `2b3755ab`
(033, reviews/2026-11-28-start-2.md) found no S1, S2 or S3 in it.
