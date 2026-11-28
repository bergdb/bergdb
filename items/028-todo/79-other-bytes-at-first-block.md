028-79. Fix: other bytes at a meta block's position, once taken, refuse a later start
=====================================================================================

Status: fix (1) built on the branch `start-fixes` (2026-11-28), in
commits of its own after 028-80's, to land after 10:30 unless Frans
says otherwise; the gates below. Kind: Fix. Frans: none; the smaller fix
goes ahead by default at 10:30 on 2026-11-28.
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


Log
---

2026-11-28. Registered by lead-1127 from the review's F2; an agent of
lead-1127 prepares fix (1) on a branch; it lands by default after 10:30.

2026-11-28. Fix (1) built on the branch `start-fixes` by an agent of
lead-1127, after 028-80, with the aborted record as a third place.
