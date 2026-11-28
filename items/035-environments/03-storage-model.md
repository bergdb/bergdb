# 035-03. The storage model: what BergDB may take for granted

Created 2026-11-28 by Frans Lundberg. Status: open: not started (after
2026.7's work is stable); notes of 2026-11-28 in section 2.

A review of what append-only storage means for BergDB, exactly, and of
what its code may take for granted from the storage under it. It is the
ground for 028-77's decision (strictly append-only files, or rewrites of
the tail at a start). Until November 2026 BergDB assumed that a crash
leaves a prefix of what was appended (014-01, section 7); 035-01 and
035-02 found two other tails after a kill of the writing process.


## 1. Scope

* **What append-only means, exactly**, at two levels: for the stream
  that the Core sees (`AppendOnlyStream`), and for the files of its
  provider `FileStream`: which operations change a file (an append, the
  delete of a whole file, and since 028-60's part 2 one truncation at a
  start's first append), and what a copy, a replica and a later
  encryption (017-10) may rest on.
* **The faults that a crash may leave**, by environment: a prefix; a
  tail of zeros within the file's length (035-01: F53's APFS after a
  kill; not on s1's ext4 or on HFS+); another file's bytes in the tail
  (035-02: APFS RAM disks and disk images, not F53's internal SSD).
  What remains to test: a power loss (035's scope: a virtual machine
  stopped hard), and environments other than F53 and s1.
* **The contract today**: 014-01, section 7 (prefix interruption, the
  provider's duty, decided for 2026.3; the broader crash model open in
  its section 6), and where 028-60 and 028-67 changed what the provider
  and the start do (the zero tail left out and cut; a tail that is not
  the stream's own refused before anything is written).
* **The result**: a fault model, each fault with the storages that can
  leave it and with who handles it (the Core by appending, the provider
  by presenting a clean end, or a person), stated in 014-01's section 7
  and in 027-14, and the ground from which 028-77 is decided.
* **Encryption and replication are requirements of the model** (Frans,
  2026-11-28), though neither is implemented: both were meant to be
  simple on append-only storage, and each exception to append-only may
  complicate them. The review states, for each fault and each way of
  handling it, what an encrypted stream and a replica by files may
  still assume.
* **Another database's nodes behind a record's own header** (028-67):
  a record whose header is its own and whose later nodes are another
  file's at the same offsets passes the checks, since a node's checksum
  covers its bytes, not its place. Node checksums that include the
  position and the database's ID would close it, a change of the
  format, decided with this review and not in 2026.7 (Frans,
  2026-11-28).
* **A deleted copy of the database's own bytes in the tail** (028-78):
  after a restore in place on a storage that can leave a deleted file's
  bytes, the bytes have the database's ID and positions and pass C3; a
  face of the third fault that no check of the bytes closes.


## 2. Notes of 2026-11-28

Notes of a discussion between Frans and a session (storage-model),
before the review starts. Nothing here is decided: each part is a
candidate for the review and for 028-77. The code was read, not run.


### 2.1. A candidate for the contract

> After a crash the forced bytes are intact, and what follows them is
> arbitrary.

* **Why.** In 035-01 and 035-02 every transaction that a force had
  returned for was intact; the wrong bytes were after the last returned
  force. No file system promises anything of bytes that are not forced,
  so "a prefix" (014-01, section 7) asks more of the storage than it
  gives. s1 confirmed the prefix for a kill of the process, where the
  operating system and its page cache survive; a power loss is tested
  on no machine.
* **One case.** The three tails of 028-77 (a cut record, zeros, another
  file's bytes) are one fault under this sentence, not three.
* **A draft in three sentences:**
  1. Every byte before a force that has returned stays as written.
  2. After a crash, the bytes after the last returned force are
     arbitrary, and at most one append long.
  3. A force that fails means that the storage has failed: the database
     stops and does not force again.
* **Frans (2026-11-28):** the sentence is a candidate. He reads Pillai
  et al. (section 2.8) first and then decides on the contract.
* **A limit, added when the notes were written:** 028-78's case. Bytes
  of a later history of the same database (a deleted copy after a
  restore in place) are among "arbitrary", and no check of the bytes
  alone tells them from the stream's own. The contract needs a stated
  limit there, or a mechanism outside the bytes; section 2.7 names one
  to examine.


### 2.2. What the code has today

* **Commits are batched in memory.** A transaction that returns is in
  the write buffer; the database's thread writes the buffer as one
  append when 2.5 MB are buffered, when a sync() waits, or after the
  buffer time, 50 ms (`Database`'s Javadoc). `FileStream` forces each
  append before it returns. So the bytes on the storage that are not
  forced are at most one append, a write of at most 5 MB (035-01,
  section 10).
* **The durable length** exists: rule D1 in `StorageManager`, which a
  sync() waits for, and `Db.getDurableLength()` in the Core. The Pub
  API has sync() and no such length.
* **The old model is stated in public text:** `Database`'s Javadoc,
  "What a crash keeps" (a power loss must leave a cut tail and no other
  bytes), and R6 of 010-04, provisional until 028-77 is decided.
* **A failed force:** `Db.sync` fails the database on a failure of the
  storage (005-30).
* **Not checked:** whether an append can span two stream files; that
  appends are issued one at a time; `FileStream`'s setting without a
  force; whether any path forces again after a force that failed;
  whether the stream marks a clean stop.


### 2.3. What follows from the contract

* **The forced position is not in the files.** The writer knows it in
  memory. A start therefore takes the last valid record as the stream's
  end, which may be a record that was written whole and not forced;
  keeping it is allowed, as it was promised neither way.
* **A bound on what a start may drop:** one largest append from the
  stream's end. Wrong bytes further back are damage of forced bytes:
  the start refuses, and a person decides. This takes the place of the
  bound of 8 MB on a run of zeros (028-60), for any bytes. It rests on
  one more assumption: a crash does not leave a file longer than the
  append asked for.
* **What cannot be told apart.** Forced bytes that the storage lost at
  the stream's end look as a tail that was never forced, and are
  dropped without an error. The bound limits how much; a start reports
  what it dropped.
* **Replication:** only forced bytes are replicated, so that a replica
  never holds a longer stream than the primary (Frans, 2026-11-28). A
  replicator copies up to the durable length. A copy of the files by
  another program does not meet the rule, as the files do not show the
  length. The rule is needed under each of 028-77's options, since a
  crash can lose bytes not forced at the source under each; so
  replication by files does not by itself separate (A) from (B).
* **"Forced" covers the file as well as its bytes:** whether a new
  stream file is durable before its directory is forced is a question
  for 035's probes (its scope: whether a directory needs a sync).
* **For the user nothing changes:** a crash keeps a prefix of the
  transactions and every one that a sync() returned for. Transactions
  not yet written to the storage were in the write buffer.


### 2.4. The order of work proposed

1. Decide the contract's sentences. Tests can show that a model is too
   weak, not that it is enough.
2. Test BergDB against the contract at the stream level, not on real
   file systems: a test provider that, at a simulated crash, puts other
   bytes in place of the tail not forced (zeros, random bytes, the
   stream's own older records, another database's bytes, a later history
   of the same database), and a check that each start gives the state of
   the last force or a later one. Deterministic, on any machine.
3. 035's probes then test one assumption per environment: forced bytes
   survive, first of all a power loss (a virtual machine stopped hard).
4. A tool that cuts the end of a `FileStream`, for the cases that end
   with a person: it keeps the bytes that it cuts and names the last
   transaction that remains.


### 2.5. Detecting the tail

* **Only near the end.** The check must be exact only within one
  largest append of the stream's end; what is before it is forced and
  the storage's (R6). A start walks the records there, and the stream
  ends at the first record that fails its check, also where valid
  records follow it. The rule for a run of zeros becomes a case of
  this.
* **What a record has today** (031-07, sections 3.3 to 3.5): a header
  tied to its position and its database (C3, 24 bits); nodes with a
  checksum of their bytes, not of their place (028-67's finding); no
  check of the got-dirty list or the padding; the last byte 10, a mark
  of the commit, not a check.
* **The candidates** are 031-07's (section 5.1): N4, the node checksums
  and one checksum a record over the database's ID, the position and
  the record's bytes; or N5, node checksums seeded with the position
  and the ID, which leaves the got-dirty list without a check.
* **The session's recommendation: N4.** One mechanism for one purpose:
  the record's checksum is the exact check of the tail, read at a
  start; the node checksums stay the best effort against damage, read
  at a load. The decisions of 2026-11-28, 07:30 (N1, GD1, M1) were
  taken under R6's provisional words and are to be seen again with the
  contract.


### 2.6. What a start does with the tail

Three ways, the first two Frans's question, the third found in the
discussion.

* **An append-only addition**, as today's fill of a cut record with
  zeros. The fill works because the cut record's header is whole, so its
  size is known. Arbitrary bytes can have no header, so a forward walk
  needs a new rule to pass them (such as: go to the next meta block's
  position). The larger cost: the bytes stay in the stream, later in
  its middle, so every walk (the start, `getTrans`, a replicator, the C
  clone, the Lean model) carries the rule and the exact check at every
  position, for ever.
* **A cut** (028-77's (B)). The tail exists only between a crash and
  the next start, and one piece of code sees it; every other reader
  sees whole records. Append-only then means: a byte below the durable
  length is written once and never changed. What follows from it:
  * the cut is by a record's check, so it belongs to recovery, not to
    `FileStream`, and the stream's interface gets an operation that cuts
    the tail, allowed only before a start's first append;
  * the fill with zeros could go too, with a cut at the cut record's
    start: one rule, used at every crash on every system, for a
    truncation on Linux where none is needed today;
  * 028-77's risk stays: forced bytes that the storage lost at the end
    are cut without an error (section 2.3).
  The session recommended the cut before the third way was found.
* **A new file at the cut's position, (D)**: a fourth option for
  028-77, not yet written there. The start writes nothing to the last
  file; it makes a new file that begins at P, the position where the
  stream ends. A file is read up to the first position of the file
  after it, so the bytes after P in the older file are never read, and
  go when reclaim deletes the file. Then:
  * the files are strictly append-only: no byte of a file is written
    twice and no file is truncated, and the exception in the rule for a
    backup by a copy of the files (`FileStream`'s Javadoc; 027-14) is
    not needed;
  * the stream is clean, as with the cut;
  * it mirrors the gap of 028-66: a file that begins after the end of
    the one before it marks a cut at the front; one that begins before
    that end would mark a cut at the tail.
  Its costs and what is not studied:
  * the files' layout changes: today every file but the last is a
    multiple of 100,000 bytes long and a file's name is its first
    position divided by 100,000; a file from any P needs names that say
    so, or begins at the multiple below P and repeats up to 100 kB;
  * a crash while the new file is made: a new file with no valid record
    is deleted or passed over at the next start;
  * a new file at every start, or only after a crash: at every start
    is the simpler rule (a start never appends to a file that exists,
    and the fill with zeros goes), but a program that starts often and
    writes little leaves many small files.
  Frans (2026-11-28): kept as a possibility.


### 2.7. Encryption: no position twice under one nonce

A cipher by position (017-10) must not encrypt two texts at one
position with one key stream. A start that writes again where a tail
was does so, unless the design prevents it. The principle for the
model: **after a crash, a position that may hold older ciphertext is
never encrypted again under the same nonce.** One key for the database
in each of the three ways below; a nonce is not secret and is stored
as it is.

* **A nonce for each file** (the session's), with (D). A read already
  finds the file that holds a position, so the Core still reads by
  position alone and the cipher stays in the provider. With a new file
  at every start it holds without conditions: no bound and no mark of
  a clean stop are needed. It changes the files' layout and is
  `FileStream`'s only.
* **A limit and dummy bytes** (Frans's). `FileStream` limits the bytes
  not forced, to 1,000,000 for example; after a crash the start cuts
  the tail and appends that many dummy bytes, not encrypted, and
  encrypts from there on; a database without encryption needs none.
  No change of the files' layout, and no dependence on the provider.
  Two corrections make the count exact:
  * the dummy is counted from the file's length E before the cut, not
    from the cut's position P: a record larger than the limit is written
    in several forced pieces, so P can be far below the last force, and
    older ciphertext can reach E plus the limit; the dummy is one
    aborted record from P to E plus the limit;
  * a crash can leave nothing to find: after a power loss a file can
    end at a record's end while the lost append's ciphertext was given
    to the device; so the dummy is needed at every start that does not
    follow a clean stop, which the stream must then mark, or at every
    start.
  It needs a cipher that knows records (headers as they are, bodies
  encrypted), since a cipher by position under the Core would turn the
  dummy's header to noise; the sizes of the records are then readable
  in the files. It keeps the cut.
* **A nonce in the meta blocks** (Frans's): a nonce for each section of
  200,000 bytes. A meta block is at a fixed position, so a reader finds
  the block of a position from the position alone; a block has about 80
  reserved bytes (031-07, section 3.2). A block's nonce is fixed once
  the block is forced, so after a crash the rest of the section that P
  lies in is not encrypted again: the bytes from P to the next meta
  block's position are a dummy, and the block written there has a new
  nonce. No bound is needed, as older ciphertext further on was under
  older nonces; the dummy is at most 200 kB; no change of the files'
  layout; any provider. What is open:
  * the crash that leaves nothing to find, as above: the skip at every
    start that does not follow a clean stop, or at every start;
  * the dummy must be passed without decrypting it: the new block can
    hold the position from which the section before it is dead, and a
    forward walk then reads the next meta block before it walks a
    section, a new rule for every walk;
  * a cold read of a node needs its section's meta block first, one
    more read; the nonce changes only at a start, so a small table of
    positions and nonces in memory removes it, and where the table is
    kept is to be designed;
  * a meta block has no checksum (M1), and a damaged nonce makes a
    section unreadable;
  * with the cut it does not give strictly append-only files; with (D)
    the new file needs a nonce of its own or the same skip.
* **The session's recommendation:** the nonce in the meta blocks is the
  one to take furthest for encryption; what a start does with the tail
  (section 2.6) is then decided on its own grounds in 028-77. No cipher
  was designed here: only that no pair of a nonce and a position is used
  twice.
* **To examine for 028-78** (added when the notes were written, not
  part of the discussion): a record's check seeded with a nonce that a
  restored database does not share with its deleted copy, such as the
  nonce of a file made at each start. The deleted copy's later records
  were then written under other nonces than the restored database's
  new file has, which no check of the bytes alone can give.


### 2.8. What others have done

Cited from memory in the discussion; none was read for these notes.

* SQLite, "Atomic Commit In SQLite", its assumptions of the hardware:
  a file's size may change before its content, so a file that grew can
  hold other bytes after a crash; the second and third tails of 028-77.
* PostgreSQL and RocksDB use their log files again, so older records
  that look valid at the end are usual there; recovery ends at the
  first record whose check, tied to its place or its log's number,
  fails, as C3 does. PostgreSQL, 2018: after a failed fsync on Linux a
  second fsync can succeed with the data not written.
* Pillai et al., "All File Systems Are Not Created Equal: On the
  Complexity of Crafting Crash-Consistent Applications", OSDI 2014:
  what each of several Linux file systems leaves after a crash, by
  operation; appends are not atomic on several, and one row of its
  table is believed to be the old model, a prefix of an append of
  several blocks. Most of its failures are of renames, overwrites and
  the order between files, none of which BergDB does. The first to
  read.
* Alagappan et al., "Protocol-Aware Recovery for Consensus-Based
  Storage", FAST 2018: telling a cut tail from damage in a log's
  middle.


## Log

2026-11-28. Created at Frans's request, with 028-77. Not started.

2026-11-28. Scope: encryption and replication as requirements of the
model (Frans).

2026-11-28. Scope: the nodes' place, from 028-67 (Frans).

2026-11-28. Scope: 028-78, a deleted copy's bytes in the tail (the
review of the start path, 033).

2026-11-28. Section 2: notes of a discussion between Frans and the
session storage-model: a candidate for the contract (the forced bytes
intact, what follows them arbitrary), what the code has today, the
detection of the tail, three ways for a start to handle it (among them
(D), a new file at the cut's position), and three ways to keep a
position from being encrypted twice under one nonce. Nothing decided;
Frans reads Pillai et al. and then decides on the contract.

2026-11-28. Renamed: the file from `03-append-only-storage.md` to
`03-storage-model.md`, the title from "Append-only storage" to "The
storage model" (Frans).
