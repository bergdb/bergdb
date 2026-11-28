028-77. Decide: strict append-only storage, or tail rewrites at a start
=====================================================================

Status: open. Kind: Decide. Frans: decision, after 2026.7's work is
stable (Frans, 2026-11-28).
Created 2026-11-28 by Frans Lundberg.

What: BergDB assumes append-only storage, with integrity and durability
the storage's (014-01, section 7; `AppendOnlyStream`'s Javadoc). A crash
while appending is the one exception that the design handles. Until
November 2026 one case was assumed: after a crash the stream is a prefix
of what was appended. Two more were found:

* **A tail of zeros within the file's length** (035-01): on F53 (macOS,
  APFS, the internal SSD) after a kill of the writing process, three
  times in about 9,500 kills of BergDB's writer and in 1 of 150 files of
  a probe without BergDB. Not seen on s1 (Linux, ext4) or on HFS+, which
  left prefixes.
* **Other bytes in the tail** (035-02): a deleted file's bytes from a
  page boundary to the last file's length, after a write that a kill
  cut, on APFS RAM disks and disk images; not seen on F53's internal
  SSD, where such pieces read as zeros.

What a start does today, case by case:

1. **A cut record** (the prefix). The start appends zeros that complete
   the record, which every walk then skips as an aborted one; a meta
   block that the end cut is completed as a block that is not valid
   (027-11, section 1.3). Nothing is written twice. This is the design
   of 2012 and the contract of 014-01, section 7.
2. **A tail of zeros.** `FileStream`'s open leaves a run of zero bytes of
   at most 8 MB at the end of its last file out of the stream, and its
   first append truncates the file where the run starts and writes there
   (028-60, part 2; Frans's decision of 2026-11-26; on `main` since
   2026-11-27, `ac33aa93`; 027-14). The layers above see a cut tail, case
   1. It is the one place where a byte of a stream file is written
   twice, and it is in the storage's provider: nothing above
   `FileStream` changed, and the Core only appends. The rule takes any
   run of zeros that ends the last file, so the zeros with which a start
   completed a cut record are left out at the next open too, when no
   record followed them, and written again as the same bytes (027-11,
   section 1.3). A run of more than 8 MB, or zeros on another storage,
   are not removed: they are recovered as a cut record where they begin
   inside the last record, and refused where they cover a record's size
   field.
3. **Other bytes.** The start refuses before it writes anything, with
   the cause, the position P and the way out: a person keeps a copy and
   cuts the stream at P (028-67's C1, exact since C3: a meta block holds
   its own position and the database's ID, a record's header a check of
   both; `BadTailException`). The automatic cut, 028-67's C2, is not
   built.

Outside the tail, a start also changes the files at the stream's front:
it deletes the files that a cut of reclaim left before a gap after a
power loss, if each one's first meta block is the database's (028-66,
C). Reclaim's cut deletes whole files in the same way while the database
runs. Neither is part of this entry's question.

Why: files that are only appended to, and removed only whole, give three
things, and a rewrite of the tail costs each of them something.

* **A copy by file-system operations while the database runs.** A copy
  that overlaps the first append after an open that left zeros out can
  hold the old file's zeros in place of bytes written after them, and is
  not a backup; 027-14 states from when a copy may begin (after an
  append of at least one byte since the open has returned). With C2 the
  same would hold for a tail of other bytes.
* **Replication by files.** A follower that copies the files as they
  grow sees the last file shrink once, and bytes at positions it may
  already hold replaced by others.
* **Encryption by position** (017-10, a later design; no stream is
  encrypted since 028-69). A committed record of ciphertext can end in a
  zero byte, so a rule that takes zeros at the end as bytes not written
  is not safe for such a stream as it stands (028-60, section 10,
  findings 1 and 2); and with a key stream by position, as the removed
  code had, a position written twice holds two texts under one key
  stream.

The other side: where a file system fails, a recovery can be impossible
in general, and detecting damage that is not a cut tail is best effort
(014-01, section 7, point 3). The aim is practical: the three known
cases, stated, each with who handles it.

Frans: decision. Two parts:

* **A model of what BergDB may take for granted from the provider of an
  append-only stream.** For each fault that a crash may leave: which
  storages can leave it (the kill of a process and a power loss apart),
  and who handles it: the Core by appending, the provider by presenting
  a clean end of the stream, or a person. 014-01's section 7 holds the
  contract of 2026.3, a prefix, with the broader crash model open
  (its section 6, decisions 1 to 5).
* **Within the model, whether the files stay strictly append-only.** The
  options:

  * **(A) Strictly append-only files.** No start truncates or rewrites.
    Case 2 is handled by appending after the zeros, which stay in the
    stream as dead bytes (115 to 459 kB in the kills of 031-02, F1; the
    dropped piece of the cut write, 035-01). Possible in principle: a record's size is at least 48,
    so no record begins with four zero bytes, and a run of zeros after
    the last whole record is recognisable; starts already pass over meta
    blocks that are not valid (028-60, part 1; 028-76). Not studied:
    every forward walk (recovery's walk of the tail, `getTrans`, a
    replicator) must skip the run, also where it begins inside a cut
    record. Case 3 is
    refused as today, or handled by a later valid meta block found past
    the bytes (since C3 a block names its position and its database);
    not studied, its soundness open. 028-60's truncation is removed, and
    with it the rule of 027-14 for when a copy may begin.
  * **(B) The provider may rewrite the tail at a start.** Case 2 as
    today; case 3 by C2: such a tail left out at the open and cut at the
    first append, as zeros are, with C1's checks deciding where. No
    person is needed after a kill on the storages of 035-02. The files
    are then append-only except for a start's first append, and the
    limits of what a copy, a replica and an encrypted stream may assume
    are stated in the contract. C2's risk as 028-67 names it: a tail
    that a storage damaged is cut without a word.
  * **(C) As today.** Case 2 truncated (F53's file system leaves it
    after a plain kill, and a database that does not start after a kill
    is S2 by 033's rules); case 3 refused, with the
    way out, C2 not built; the one rewrite stated in 027-14 as it is.

  No recommendation yet: the review of what append-only storage means
  (035-03) comes first.

Decided so far (Frans, 2026-11-28): 028-67's C2 is held until this entry
is decided; case 2 stays as it is in release 2026.7.

Taken with this entry (Frans, 2026-11-28): another database's nodes
behind a record's own header. Since C3 a meta block and a record's
header are tied to their place and their database; a node is not. A
record whose header is its own and whose later nodes are another file's
at the same offsets passes the checks, and with two databases of
identical layout a start took the other database's value of one key
(028-67, "Found, not covered by C3"). Node checksums that include the
position and the database's ID would close it: a change of the format,
decided with this review, not in 2026.7. The same gap gives 031-08's
UB-4 (part B, 2026-11-28): another database's stream file in the middle,
of the same name and length, is accepted, and reads give its values.

Also with this entry (2026-11-28): 028-78, a deleted copy of the
database's own later bytes in the tail (a restore in place on a storage
of 035-02): a face of case 3 that no check of the bytes closes, since
the copy has the database's ID and positions (the review of the start
path, 033, `reviews/2026-11-28-start.md`, F1).

Done when: the model is written (035-03, and from it 014-01's section 7
and 027-14), Frans has chosen among (A), (B) and (C), and 028-67's C2 and the
check of the nodes' place are decided with it; work that the choice asks for becomes entries or
subitems of its own.

First step: 035-03's review.


Log
---

2026-11-28. Registered by lead-1127 at Frans's request; C2 of 028-67
held (Frans). To be taken up after 2026.7's work is stable.

2026-11-28. The nodes' place (028-67's finding that C3 does not cover
nodes) is taken with this entry (Frans, 07:30).

2026-11-28. 028-78 (a deleted copy's bytes pass C3) named as taken with
this entry.
