028-67. Fix: a deleted file's bytes in the last stream file after a kill
=======================================================================

Status: decided; C1 and C3 built (2026-11-27, below), T1 of 031-06's
review 3 fixed (2026-11-28, below), open: C2, held (Frans, 2026-11-28)
until 028-77 is decided, and with it the nodes' place ("Found, not
covered by C3", below). Kind: Fix. Frans: decided.
Created 2026-11-26 by Frans Lundberg.

What: on APFS, a write cut by a kill of the process (or one that fails
with EFAULT, which cuts it the same way without a kill) can leave, from
a page boundary to the last file's length, the bytes of a file deleted
before, not zeros (035-02, sections 6 and 7): seen on APFS RAM disks and
disk images, in most cut first writes of a new file; not seen on F53's
internal SSD in 63 cut first writes of a new file and 476 failed
copies, where they read as zeros. In BergDB the deleted file is an
older stream file, deleted by a cut of reclaim, or another database's
file on the same volume; every stream file begins at a multiple of
200,000, so an older file's meta blocks can lie exactly at the last
file's meta positions. Nothing in a meta block or a record ties it to
its position or to its database.

Why: a start today refuses most such tails with messages that name
neither the cause nor the way out ("Invalid magic bytes in stream",
"The meta block at P names the last transaction at S, which cannot be
one", "Bad transaction size", "Bad lastByte", "is not committed", a
checksum); some starts first append zeros for a size read from the old
bytes, up to 2 GB, before they refuse or succeed (035-02, section 10).
No start took another file's records as its own in the constructed
cases, but nothing rules it out (035-02, section 10.1). A database that
does not start after a kill is S2 (033's rules); data from another file
would be S1. 028-60's options are about zeros; these tails are not
zeros, so a cut of zeros never takes them.

Frans: decision, between (035-02, section 11, in full):

* **C1. Refuse with the cause and the way out, before writing.** In the
  last file, a meta block that names a record before the stream's first
  position, or of another database, is not valid; other bytes at a meta
  position, a size that cannot be one, a bad last byte or a checksum
  after the last valid block mark a tail that is not the stream's own,
  from P, the end of the last right record. The start refuses with one
  message that names the cause (a kill during an append on APFS can
  leave such bytes) and the way out (keep a copy, cut the file at P
  less its first position). The recovery completes a torn last record
  with zeros only after the Core has found its header to be one, so
  that no size from other bytes makes the start append up to 2 GB.
  About 80 lines and tests, no format change; the header check needs a
  hook from the Core into recovery. A person still cuts the file.
* **C2. Cut such a tail, as 028-60's B2 cuts zeros.** C1's checks and
  B2's conditions, then the start cuts at P and goes on. Risk: a tail
  that a storage damaged is cut without a word, and a record of another
  file that passes every check is taken, as today.
* **C3. Tie meta blocks and records to their place.** A meta block
  holds its own position; a record a check of its position and the
  database's ID. A block or a record of another file or place is then
  not valid, and C1's and C2's checks are exact. A change of the stream
  format (027-03), for new databases; a few bytes.
* **C4. Keep older bytes out of new files** (`FileStream` writes a new
  file's whole size in zeros first, or the cut zeroes a file's meta
  positions before deleting it). Not recommended: it doubles what is
  written, or covers only the meta blocks.

Recommendation, 035-02: C1 now, with 028-60's part 2, and C3 with the
next change of the stream format (032), after which a cut is exact.

Done when: Frans's choice; with C1, the refusals name the cause and the
position to cut at, and a torn record's header is checked before the
start fills, with unit tests from 035-02's kept files (zeros, an older
stream file's bytes at the same offsets and at others, another
database's blocks, a size from other bytes), each refused with the
message and nothing written, and each file cut at P then starting;
`java/before-commit.sh` printing `BEFORE COMMIT OK`; 027-11's start
steps and `Database`'s Javadoc ("What a crash keeps") updated.

First step: 035-02, sections 10 and 11; 028-60, sections 2 and 4;
`RecoverableStream`'s recovery (`readLastValidMetaBlock`,
`fixLastTransactionIfNeeded`).


Decision
--------

Frans, 2026-11-27 (15:50 to 16:02): **C1 and C3**, both in release
2026.7, whose stream format changes anyway (031-06) and which does not
open a database of 2026.6 (031-06, section 8, A3).

* **C3, the meta block.** A meta block holds its own stream position, in
  8 of the 81 bytes reserved at offset 46. A start takes a block as valid
  only if that position is the one it was read at and its database ID
  (16 bytes at offset 24, written in every block today and compared with
  nothing) is this database's.
* **C3, the record.** The record header's three unused bytes (5 to 7,
  after the format byte; written zero today and not read) hold a check:
  CRC-32C over the database's ID, the record's own stream position and
  the header's other fields (the size, the time, the startup position,
  the top position), truncated to 24 bits. The field ties the record to
  its place and its database, and covers the header, which has no
  checksum today (027-03, G12). It is computed when the record is
  written and compared at each parse of a record (`StoredTrans.Parser`,
  at a start and where a record is read). Neither structure grows. A
  wider check (32 or 64 bits) would grow the 32-byte header by 8 bytes a
  record: not taken; the width is reviewed with the stream's other
  checksums (031-07).
* **C1.** A tail that fails these checks is refused, with the cause and
  the way out, before anything is written: no zero fill from a size
  read out of such bytes.
* **C2 is not decided**: such a tail left out at the open and cut at the
  first append, as zeros are since 028-60's part 2 (old bytes at the
  tail are a third face of a partial append). It is decided after C3 is
  in and tested. Held since 2026-11-28 (Frans): C2 would be a second
  rewrite of the tail at a start, and whether a start may rewrite the
  tail at all is 028-77's question; C2 is decided with it, and not built
  before. **C4 is not taken.**

Why three bytes suffice: a stale record is taken only if it begins
exactly where a record of the stream ends, passes the 24-bit check (1 in
16.7 million for bytes of another place or database) and then every
check that exists today (the format byte, the sizes, the node checksums,
the last byte, the meta block's).

Where it is built: in 031-06's landing, with the format's other changes
(031-06, section 9, step 4). Done when the checks are in, with the tests
named above, and C2 is decided.


Built
-----

2026-11-27, by an agent of lead-1127 on the branch `028-67-c3` (from
`main` at `5d6fe4ae`; on `main` as `b0aac3a9` and `53ff486f`, after
the review's fixes, `48203205`), for 031-06's landing,
step 4. C1 and C3 as decided; C2 not built, C4 not taken.

* **C3, the meta block.** Version 156 (`MetaBlock.VERSION_156`); bytes
  46 to 53 hold the block's own stream position, written with each block
  (`RecoverableStream.writeMetaBlock`). A block is the stream's
  (`MetaBlock.isOwn`) if it is valid, holds the position it is read at,
  and holds the database ID of the stream's first block, the first at or
  after the first position (`readFirstMetaBlock`): that block must be
  valid and hold its own position, and its magic and version are refused
  as before (`BadMagicBytes`, `VersioningStreamException`). Every search
  for a block, at a start and after (`readLastValidMetaBlock`,
  `getPosOfTransCompletedBefore`, `getRecordStartBefore`), takes only the
  stream's blocks: a block after the first of other bytes, of another
  version, place or database is passed over, as a block of zeros is
  (`readOwnMetaBlock`), and the walk below refuses such a tail where it
  matters.
* **C3, the record.** Bytes 5 to 7 of the header hold the low 24 bits of
  CRC-32C over the database ID (16 bytes), the record's position (8,
  little-endian) and the header's bytes 0 to 4 and 8 to 31, little-endian
  (`StoredTrans.headerCheck`), set by `Serializer.serializeToBuffer`
  (`NodeStream.appendNodes` gives the serializer the ID) and compared by
  `Parser.parse` after the format byte; `StoredTrans.parse` and
  `Parser.parse` take the ID (`NodeStream.databaseId()`). Record format
  9 keeps its number (no release has written it); its Javadoc and 027-03
  say what changed.
* **C1.** `RecoverableStream.recover(RecordCheck)` walks the records from
  the one the last valid block names to the end before it writes anything
  (`walkTail`; the cut meta block's completion and the zero fill come
  after it), with the Core's check as a hook (`StoredTrans.RECORD_CHECK`):
  each size 5 or more, each whole record's last byte 0 or 10, each
  committed record's header holding its check, and the header of a
  record that the end cuts holding it before the fill (cut within its 32
  bytes: a size the writer writes, 48 or more and a multiple of 8, and the
  format byte 9 if there). The first record walked is refused for another
  format first, as before; the stream's last record, if committed, and
  the committed record before the first that fails are parsed whole, as
  another file's bytes can begin inside a record after its own header (so
  a start reads and parses its last record twice; not timed). A
  tail that fails is refused with a `BadTailException` (a
  `StreamFormatException`) whose message gives the cause, then P (the end
  of the last record that is one, or the start of the record parsed
  whole if it does not parse) and the way out, for example: "The header
  of the record at 512 is not one of this database's records at its
  place (bergdb 028-67, C3). The stream's records end at stream position
  512: from there to the stream's end, ..., it holds bytes that are not
  its records. A kill of the process during an append can leave such
  bytes in the last stream file, within its length: zeros, or the bytes
  of a file deleted before, such as an older stream file or another
  database's, as on macOS (APFS; bergdb 028-67, 035-02); so can a
  storage that loses or damages bytes. The start has written nothing. To
  start the database, keep a copy of its files, then cut the stream at
  512: cut the stream file that holds it to 512 less the file's first
  position, which is the number in its name times 100,000, and remove the
  later stream files, if any; the stream's bytes from there on are
  lost." Zeros past a record's end keep the first sentence, "Bad
  transaction size in db stream, 0, spos P. Stream length: L."
* **Older databases.** The mechanism is the meta block's version: a
  database of `main` before this change (version 155, headers without
  the check) and one of release 2026.6 are refused by the stream's first
  block before anything is written: "Cannot read meta block with version
  155. Version supported: 156. Version 155 is a database written by
  BergDB release 2026.6, which this release does not open: there is no
  upgrade path, and release 2026.6 still opens it (bergdb 031-06); or by
  a development build of 2026.7 before 2026-11-27, whose meta blocks do
  not hold their own positions (bergdb 028-67). The start has written
  nothing." Release 2026.6 refuses 156 as a newer version's.
* **Tests.** `DbTesterTail` (new): stale tails on CorruptStreamTester's
  workloads from every page of 4,096 bytes (unit) and every 512 bytes
  (f): zeros, another database's bytes (another ID) at the same
  positions and 4,096 after, the stream's own bytes from 4,096 and
  200,000 before, and a size of 1 GB at each record after the last meta
  block; the same on a file database's last file of 1 MB (f): zeros, an
  older stream file at the same offsets and at others, another
  database's last file and that file 4,096 bytes on, a size of
  100,000,000; each start takes exactly the records that end before the
  first byte that differs, or is refused with the message, nothing
  written (every file byte for byte), and the stream cut at P (the file
  cut at P less its first position) starts with them, writes and starts
  again; 028-67's S1 case (031-07's probe: another database's stream
  from 512) refused at 512; a torn last record whose size reads 1 GB
  refused, and a header cut by the end at 1 to 31 bytes completed, or
  refused for another format byte; another database's, another place's
  and an older file's meta block passed over. `StoredTrans`:
  `testHeaderCheck` (the CRC as specified; another position or ID; every
  bit of the header), `testRecordCheck`; `MetaBlock.storedPosAndId`. The
  tests that set a header field to reach a later check
  (`DbTesterRestart`) set the check again (`writeHeaderField`), and the
  version tests take 156 and 157. CorruptStreamTester: its KNOWN no
  longer has 015-73, 019-30 and 019-31, which the check refuses; its full
  set on seed 20768 (485,809 copies): 0 failures, no copy taken as known
  (031-07's run on `main`: 171 of 019-30, 18 of 019-31, 1 of 015-73) and
  no zero fill past 1 MB.
* **Found, not covered by C3 as decided.** A record whose header is its
  own and whose later nodes are another file's at the same offsets passes
  the checks: the node checksum covers a node's bytes, not its position
  or database (031-07, N1). Made with a variant of `testStaleTailFiles`
  in which the two databases have the same value sizes, and so the same
  record and node layout: the last file held the other database's bytes
  from its offset 278,528 (the first byte that differs at stream position
  10,279,200); the start refused at 10,279,488, the record after, and the
  stream cut there held the other database's value of `k805`, whose
  record (to 10,279,487) those bytes began in after its header. The
  test as committed gives the two databases other value sizes. Closing
  it needs a check of the nodes' place, such as each node's CRC-32C begun
  with its position and the database ID (035-02's first form of C3), a
  change of the format. Decided (Frans, 2026-11-28): taken with 028-77's
  review (035-03), not in 2026.7; the node checksums stay as they are
  (031-07, N1).
* **Not changed.** The Lean model, the contract and its checkers and the
  trace format (027-02): none reads a header's bytes or a meta block
  (031-07, section 6); `TraceExport` and `RestartInvariance` pass the ID
  to the parse. `RecoverableStream.holdsFirstTransactionAlone` and
  `isIncompleteCreation` read a size without a check, as before: a size
  of other bytes at the second record of a stream under 200,000 bytes
  reads as a creation that did not complete. 028-70's case (a last
  committed record of another format) is refused now before the recovery
  writes: by the format if it is the first record walked, as
  `NodeStreamTester.testStartRefusesFormat8` shows, else by its header's
  check. The C clone (012, 022) follows a
  release.
* **Gates** (in the branch's clone, F53, beside other sessions' runs):
  * `java/before-commit.sh`: `BEFORE COMMIT OK (78 s)` on `b0aac3a9`,
    `BEFORE COMMIT OK (86 s)` on `53ff486f`.
  * `java/stress/level2.sh` (full): `LEVEL 2 OK` (16 min), on `b0aac3a9`.
  * `java/stress/level3.sh`: `LEVEL 3 OK` (15 min), on `b0aac3a9`.
  * `java/stress/level4.sh quick`: `LEVEL 4 OK`; `java/stress/apps.sh
    quick`: `APPS OK`; both on `53ff486f`.
  * CorruptStreamTester's full set, seed 20768, on `53ff486f`: 0
    failures.
  * 031-06's `probes/faults.sh` and `probes/sweep.sh` do not run on this
    branch, nor on `main`: `NoSuchMethodException` for
    `Db.maintain(int, int)` (the review's R6, fixed on
    `031-06-review-fixes`). `FaultProbe` compiled with
    `review-main-probes/P2CrashProbe.java` (its two lines of
    `maintain(int, int)` left out), faults.sh's six seeds: the output of
    `main` at `5d6fe4ae` line for line, but for the digests and the
    positions of the first byte that differs; its continuations counted
    bad (plan-stop and plan-fail at parts, among others) are the same on
    `main`. `review-main-probes/run.sh sweep` (P2CrashProbe): 12,105
    interruptions and 2,142 torn records, 0 different, as on `main`.
  * `lean/contract/gate.sh`: not run; nothing in `lean/` changed.
* **Gates on the combined tree** (2026-11-27, the lead, with the
  commits on `main`'s `48203205`, 031-06's review fixes; the `java/` and
  `lean/` of `b0cb561c` are the same): `BEFORE COMMIT OK (77 s)`,
  `LEVEL 2 OK`, `LEVEL 3 OK` (C-STEP 0 of 23,127, C-CUT 0 of 869);
  031-06's `probes/sweep.sh`, which runs again since the review's R6 was
  fixed: 0 different in all 62 result lines; `probes/faults.sh`: bad 0
  in all 42 lines.
* **Fixed (2026-11-28): T1 of 031-06's review 3** (high): a start
  refused the tail that the recovery of an earlier start had written
  when it completed a record that a crash cut in its header. The walk
  took a record that the end of the stream cuts only if its first 32
  bytes held the header's check, or if the end cut it within them (a
  size the writer writes and the format byte 9 as far as they went); the
  completion wrote the filler 4 at byte 4 after a cut at 1 to 4 bytes,
  zeros after a longer one, and completed a size field to 17 or more. So
  every later start refused, with a `BadTailException`, nothing written:
  (a) on a file database, a cut 1 to 4 bytes into the last record, a
  start, a stop with no commit, as `FileStream`'s open leaves the
  completion's zeros out (028-60, part 2); (b) the same for a cut at up
  to 24 bytes when the completion crossed a meta block; (c) a kill
  during the completion, on any storage; (d) zeros from header bytes 4
  to 31 on a storage that keeps them (for `FileStream` a run of more
  than 8 MB). `b0aac3a9`'s parent started every one. The review's probes
  (`review-3-probes/`, `run.sh OUT tail`) on `main` at `50c60f13`:
  `S4RestartAfterTornSizeProbe` start 2 refused after cuts 1 to 4,
  `S4TornSweepFileProbe` 58 of 1,016 refused, `S4TornFillProbe` 216 of
  308, `S4TornFillFileProbe` 24 of 109.
  * **The rule** (027-03, section 7, "A cut record" and "The
    completion"; 027-11, section 1.3): zeros at the end of a cut record
    are bytes not written, as `FileStream`'s open takes a run of zeros
    at the end of the last file. The walk takes a record that the end
    cuts if its header holds its check, or if its bytes up to the last
    that is not zero (its size field's at least) are fewer than 32, begin
    a header as far as they go (a size the writer writes, or of a size
    field cut short a first byte that is a multiple of 8; the format byte
    9 if there), and are followed by zeros only to the end of the stream
    (`RecoverableStream.tornRecordIsOwn`; `RECORD_CHECK.tornHeaderFits`
    from 1 byte on). The completion writes zeros only after a cut size
    field's missing bytes, the first of them 1 if zeros give less than
    48 (`MIN_TRANS_SIZE`, 17 before, now the Core's least record;
    `TORN_HEADER_FILLER` gone), so every part of it that a later start
    finds is again such a record and is completed to the same bytes. The
    other choice, a completion that writes a header holding its check,
    was not taken: it cannot be made for a cut after byte 7, whose check
    bytes are written, and it leaves case (d) open, whose zeros no start
    wrote. What C1 refuses stays refused: a header of 32 bytes that does
    not hold its check and has bytes that are not zero after its zeros or
    from byte 31 on, another format byte, a size the writer does not
    write, and, new, a cut size field whose first byte is not a multiple
    of 8 (refused at the first start: its completion would give a size
    that a later start refuses). A foreign tail of a fitting header's
    begin and zeros only is completed and aborted, as a cut header was
    before; no record of it is taken.
  * **Tests.** `DbTesterTail.testCompletionTakenLater` (MemoryStream)
    and `testCompletionTakenLaterFiles` (a file database), the last
    record after "a" alone and over a meta block, cut at each of its
    first 40 bytes: start 1, then a start after a stop (on files two),
    each holding "a" and not the record's key, the stream byte for byte
    start 1's; the completion cut by a kill at each byte to the
    record's 40th and at later positions, around the meta block too,
    then started, the stream start 1's but for a meta block that the
    kill cut (completed as an invalid block); zeros from each header
    byte 4 to 31, two starts. Their `Full` forms (night tests) kill
    after every cut; `testLongZeroRunInHeader` (night) has zeros from
    header bytes 4 to 31 over 9 MB, the meta blocks in them zeros too.
    `testTornRecordHeaderChecked` also refuses a cut size field of an
    odd first byte and a header of zeros followed by other bytes;
    `StoredTrans.testRecordCheck` the fit from 1 byte and
    `MIN_TRANS_SIZE` the least record; `RecoverableStream`'s
    `testTransHeaderFixBytes2` and `crashInTransactionSize` the size of
    48. The new tests fail on `main` before the fix.
  * **Probes after the fix**: `S4RestartAfterTornSizeProbe` every cut 1
    to 8 three starts ok; `S4TornSweepFileProbe` ok 1,016, bad 0;
    `S4TornFillProbe` ok 308, refused 0; `S4TornFillFileProbe` ok 109,
    not ok 0. (`S4TornSweepProbe`'s 2 bad, at 369 and 466, are as on
    `main`: its first position, 272, is read before the creation's
    second record and the record of "a" (416 to 512) reach the stream,
    so the cut at 369 is in the creation's second record, refused as a
    creation that did not complete (028-18), and the cut at 466 in the
    record of "a"; not T1.)
  * **Gates** (in the branch's clone, F53, beside other sessions' runs):
    `java/before-commit.sh`: `BEFORE COMMIT OK (81 s)`;
    `java/stress/level2.sh`: `LEVEL 2 OK`; `java/stress/level3.sh`:
    `LEVEL 3 OK` (C-STEP 0 of 23,127, C-CUT 0 of 869); 031-06's
    `probes/sweep.sh`: 0 different in all 63 result lines, `SWEEP DONE`;
    `probes/faults.sh`: bad 0 in all 42 lines, `FAULTS DONE`;
    `java/stress/kill-restart.sh 1000`: `KILL RESTART OK: 1000 kills and
    50 exits`; the review's four probes as above.


Log
---

2026-11-26. Registered by lead-1126, from 035-02, section 11.

2026-11-27. Decided by Frans (15:50 to 16:02): C1 and C3 in 2026.7,
built in 031-06's landing; C2 after C3 is in and tested; C4 not taken.

2026-11-27. C1 and C3 built by an agent of lead-1127 on the branch
`028-67-c3` (section Built); not landed; C2 open.

2026-11-28. T1 of 031-06's review 3 fixed by an agent of lead-1127 on
the branch `028-67-t1` (section Built).

2026-11-28. C2 held (Frans) until 028-77 is decided: strictly
append-only files, or rewrites of the tail at a start. A tail that is
not the stream's own stays refused, with the way out named.

2026-11-28. The finding that C3 does not cover nodes goes with 028-77's
review (Frans, 07:30): a check of the nodes' place is a change of the
format, not made in 2026.7.
