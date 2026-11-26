028-67. Fix: a deleted file's bytes in the last stream file after a kill
=======================================================================

Status: open. Kind: Fix. Frans: decision.
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


Log
---

2026-11-26. Registered by lead-1126, from 035-02, section 11.
