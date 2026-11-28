028-78. Decide: a deleted copy of the database's bytes in the tail pass C3
==========================================================================

Status: open. Kind: Decide. Frans: decision, with 028-77's review
(035-03).
Created 2026-11-28 by Frans Lundberg.

What: since 028-67's C3 a meta block holds its own position and the
database's ID, and a record's header a check of both, so that a start
takes no block or record of another database or place
(`MetaBlock.isOwn`, `StoredTrans.headerCheck`). A copy of the database's
own files has the same ID and the same positions: its later records and
blocks, at the positions where they were written, hold their checks in
the database that it was copied from. The review of the start path of
2026-11-28 (033, `reviews/2026-11-28-start.md`, F1) showed on
constructed images that a start takes such bytes, or names a cut that
loses committed records. Severity S1 (033's rules) where it applies; it
needs both of:

* **The environment of 035-02:** a kill that cuts a write can leave a
  deleted file's bytes in the last stream file, from a page boundary to
  the file's length (seen on APFS RAM disks and disk images, not on
  F53's internal SSD).
* **A deleted copy of the database's later files on the same volume**,
  as a restore of a backup in place leaves: the database's files are
  deleted, the backup's put in their place, and the database is started
  and written. The deleted files hold what was committed after the
  backup, at the positions where the restored database writes next, and
  the deleted stream files after the backup's last have the names of the
  files that the restored database makes next.

How: the review's two probes
(`reviews/2026-11-28-start-probes/`), with A the deleted files' database
and B the restored one. Three outcomes, by where A's bytes begin:

* **The refusal's P is before committed records**
  (`StaleFirstBlockProbe OUT sameid exact`). A's block at a meta position
  among the bytes is valid, with B's ID and its own position; the start
  takes it as the last valid block and walks from the record that it
  names, a position in A. B has no record's start there, so the walk
  refuses with that position as P: B's last committed record ends at
  400,000, the message says that the stream's records end at 397,512,
  and the stream cut at P as the message says has lost two synced puts.
* **A's records are taken** (`StaleCopyProbe OUT restore` and `same`).
  Where A's bytes begin at a record's start of both and their times
  follow B's, the start takes A's records: of B's 8 keys, 8 read a value
  that A wrote after the copy. The database holds transactions that the
  restore undid.
* **Refused with no way out** (`StaleCopyProbe OUT earlier`). Where A's
  records are earlier than B's before them: a `StreamFormatException`
  ("non-increasing tt"), with no P; the files as before.

Why: no check of the bytes alone can tell A's bytes from B's. The
deleted files held a later history of the same database: a stale record
at the restored stream's end has this database's ID and its own
position, its header holds its check, and it follows the same record
before it as B's own next record would. A check of the record before it
(a chain) does not separate them either where A's bytes begin right
after the backup's end. `Database`'s Javadoc ("What a crash keeps") says
that "a start takes no meta block or record of another file or place";
that holds for another database or place, not for another file of the
same database. It is beside 028-67's "Found, not covered by C3" (a
record whose later nodes are another file's, taken with 028-77): there
the header is the database's own, here the whole record or block is a
copy's. 2026.6 checks neither the place nor the ID, so the case is not
new with C3: it is what C3 leaves open (not a released bug of its own).

Frans: decision. The options:

* **(a) The storage's to prevent; a stated limit.** A storage that
  returns a deleted file's bytes after a kill is outside what BergDB
  assumes of its storage (010-04, R6, provisional until 028-77), and C3
  is a best effort that closes the cases of another database and
  another place. The limit is stated under R6's cases and in
  `Database`'s Javadoc where it describes a backup and its restore:
  restore into a new directory or onto a new volume, not over the
  deleted files of the same database; and after a refusal that names P,
  cut nothing by hand on a volume that held a deleted copy before the
  copy's files are known to be gone. No change of the code or the
  format. The cases stay: on such a storage, after a restore in place, a
  kill can bring back transactions that the restore undid.
* **(b) A restore makes a new incarnation.** The stream holds a value
  from the restore on (an incarnation number or a random value, written
  by a restore tool or a call that a restored database must pass
  through), and every later record's header and meta block is tied to
  it as it is to the ID today. A's later bytes hold the old value and
  fail the check in B. A change of the stream format (the header's and
  the block's checks, and a record or block that changes the value) and
  of the public API or the tools (a restore that BergDB knows of); a
  copy made by file-system operations and started as it is would stay
  uncovered, so the rule "a restored copy is started through the
  restore" becomes part of the contract. The review names two shapes of
  such a value: an ID of the start that wrote the bytes (then every
  start changes it and no restore call is needed, but the bytes after a
  start depend on a value that is not in the stream before them, which
  the deterministic stream of 031-06 excludes), or the check of the
  record before (a chain, which does not separate the copies right
  after the backup's end).
* **(c) New stream files are zeroed before use.** 028-67's C4: a new
  file is written with zeros and forced before a record goes into it, so
  that a cut write leaves zeros, which a start recovers (028-60). Closes
  the fault at its source for every kind of other bytes, with no change
  of the format. Not taken on 2026-11-27 for its cost (each stream file
  written twice, and the first write of up to 20 MB before the file
  takes a record, against P1); it does not cover a storage that brings
  back other bytes inside a file already zeroed.

Recommended: taken with 028-77, whose review (035-03) states what a
storage may leave and who handles it; (a) meanwhile, as the state of the
code. It is a face of 028-77's case 3 that no check of the bytes closes.

Done when: Frans has chosen with 028-77; the limit is stated in the
Javadoc and under R6 (a), or the work of (b) or (c) is an entry or a
subitem of its own.

First step: 035-03's review, which names this case.

Found by: the review of the start and recovery path of 2026-11-28 (033,
`reviews/2026-11-28-start.md`, F1), by probes on constructed images.


Log
---

2026-11-28. Registered by lead-1127 from the review's F1; for Frans,
with 028-77.
