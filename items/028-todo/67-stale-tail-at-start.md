028-67. Fix: a deleted file's bytes in the last stream file after a kill
=======================================================================

Status: decided, open until built. Kind: Fix. Frans: decided.
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
  in and tested. **C4 is not taken.**

Why three bytes suffice: a stale record is taken only if it begins
exactly where a record of the stream ends, passes the 24-bit check (1 in
16.7 million for bytes of another place or database) and then every
check that exists today (the format byte, the sizes, the node checksums,
the last byte, the meta block's).

Where it is built: in 031-06's landing, with the format's other changes
(031-06, section 9, step 4). Done when the checks are in, with the tests
named above, and C2 is decided.


Log
---

2026-11-26. Registered by lead-1126, from 035-02, section 11.

2026-11-27. Decided by Frans (15:50 to 16:02): C1 and C3 in 2026.7,
built in 031-06's landing; C2 after C3 is in and tested; C4 not taken.
