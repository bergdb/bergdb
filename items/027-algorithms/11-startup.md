# 027-11. Startup

Created 2026-11-13 by Frans Lundberg. Status: reviewed (2026-11-13), for
Frans to read.

Part 7 of 027 (027-04, section 2.3; Levels 1 and 2): from the stream to a
running database. The rule as `main` has it at c82bce56 (2026-11-13),
read from the code; sections 1 to 4 and 6 to 8 checked against `main` at
8a0897cf (2026-11-28) for the changes since release 2026.6. It replaces
027-01's `sis-model.md`, section 6.2, and `levels.md`, section 4 and the
startup points of section 5. The bytes are
027-03's (sections 6, 7, 8 and 14); T1 to T4, the take, D, Rule A and the
startup pos policy are part 6's (027-10; until it is written, 027-01's
`sis-model.md`, sections 5 and 6.1); a first touch after a start is part
8's; reclaim's part of a start is 027-13, section 1.9. Each claim carries
one status word of 027-04, section 2.2.


## 1. What it does

A start makes a running database of the end of the stream. It completes
a torn last record as an aborted one, finds the startup pos s in the
last record, reads the startup section, makes the canonical objects of
the section's index nodes, finds the super root at the startup time,
reruns the section's transactions, rebuilds D from the stored got-dirty
ids and links D's pointers (rule 4). Every other node is read at its
first touch. A start appends nothing but a new database's creation and
recovery's fill, which it holds in memory until its last check of what
it reads (1.3, 1.9; 028-70, 2026-11-28); a cut that reclaim makes at a
start (1.9) may delete stream files, and appends nothing. Since 031-06
(2026-11-27) each record's maintenance is decided from the stream before
it and its action (031-06, section 2, rules 1 and 3), so a start has
none of reclaim's work to complete: it reads reclaim's state off the
stream (1.9) and writes nothing for it.

### 1.1. Terms and constants

* **R(i), T(i)**: record i and its transaction; **k**, the last
  committed record. **M** 128, a meta block's size; **MD** 200,000, the
  meta block distance (027-03, section 6).
* **s**, the startup pos: R(k)'s startupPos, a record's position (0 is
  read as 128, the first record). **ts**, the startup time, R(s)'s time.
  **The startup section**: R(s), ..., R(k); T(s) is not rerun. **sd**:
  the startup distance, the KV `/#i/-sd` (since 028-15;
  until then the last valid meta block's).
* **topPos**: R(k)'s position of the newest written top node. **gd(j)**:
  R(j)'s got-dirty pairs (id, position). **prevPos**: the position of
  the version before, which a key node version names. A **vpos** (odd)
  is the id of a node not yet written; the nodes that T(j) makes get the
  vpos after R(j)'s position, in the order made.
* **Rule R**: a pointer to a node with a version in R(s), ..., R(k)
  names its newest version there, whatever position it holds. **Rule
  4**: each pointer of a node of D to a node with a canonical object
  holds that object's handle.

### 1.2. The checks before recovery

In this order, under the write lock and `readSync`; from step 2 on, a
refusal has written nothing:

1. **An empty stream** is created: meta block 0 (lastTrans −1, the
   node size, the builder's id or a random one, the time, its own
   position 0 since 028-67; sd too until 028-15) and the
   primordial record, a super root and an empty key node: 272 bytes
   (`Db.CREATION_LENGTH`, asserted at the creation; 264 until 024-25,
   26c21000). The creation's second record, the startup distance's, is
   written at the end of the start (1.9); with `created.txt` (the Pub
   API) both are synced then, and `created.txt` written after the sync
   (015-01, 028-18; until 028-18 the primordial record was synced and
   `created.txt` written here).
2. **An incomplete creation** is refused (`DatabaseNotCreatedException`,
   005-33): a stream not cut and not longer than the creation, whose
   bytes begin as a meta block of this version; its block, if complete,
   valid and naming no record; its record, if begun, cut, or failed.
   Since 028-18 (option C), on a start that did not create the stream at
   step 1, also the primordial record committed and alone: a stream not
   cut and shorter than a meta block distance, its first block valid and
   naming no record, its first record of the creation's length and
   committed, and after it nothing, a part of a record, or one record
   failed that ends the stream (`RecoverableStream.holdsFirstTransactionAlone`).
3. **The last valid meta block** B: of the blocks complete in the
   stream, from the last down to the first at or after the first
   position, the first that is valid: its last byte 10, its own position
   at offset 46 the one it is read at, and its database id that of the
   stream's first block, the first valid one at or after the first
   position (028-67, C3; Frans, 2026-11-27; blocks that are not valid
   before it passed over since 2026-11-28, as recovery's completion of a
   block that a kill cut or a block of zeros leaves one at the front of
   a cut stream). Each block read up to it must have the magic and the
   version 156 (155 until 028-67, whose streams, of 2026.6 and of builds
   of 2026.7 before 028-67, are refused with a message that names them;
   154 until 028-15, 2026.5's and before), or be zeros: else a
   `StreamFormatException` (SFE) that names the causes (020-28), or a
   `VersioningStreamException` (005-40); and the first valid one must
   hold its own position, else none is valid. After it, a block of 128
   zero bytes (as a zeroed tail leaves it, 028-60), of other bytes or
   another version, or of another place or database (as an older stream
   file's or another database's bytes in the last file after a kill
   leave it, 035-02) is not valid and passed over. B's time must not be
   negative (checked at the search for s, 1.4, `MetaBlock.checkFormat`).
   None valid: an SFE; for a stream whose first position is
   after 0 its message says that the stream may lack bytes that the
   database needs, with the storage's account of its front (028-66; for
   `FileStream` it names a gap in the files, 027-14).
4. **Its node size**: 0 or above 62 is a damaged block (0 was a stream
   before 2026-10-27 until 028-15, 005-50); another than the start's (30
   but in tests, 026-08) is refused.
5. **Its lastTrans**: −1, or from max(128, the first position) to below
   the block (019-34); else an SFE. One from 128 to below the first
   position is refused as a stream that lacks bytes the database needs,
   from that record on, with the storage's account (028-66,
   `RecoverableStream.checkLastTransSpos`).
6. **The files before a gap** (Frans, 2026-11-27; 028-66, section 6.2):
   the bytes that the storage holds before its first position and deletes
   at the next cut, `FileStream`'s files before a gap in its files (027-14),
   are given to the start one by one, oldest first
   (`AppendOnlyStream.checkLeftovers`); each one's first meta block must be
   of this version, valid, with its own position and B's database id
   (`RecoverableStream.leftoverProblem`), else the start is refused, a
   `StreamIoException` whose cause, for `FileStream` a
   `BadDirStateException`, names the file, what its block holds and the way
   out. The storage deletes none of them before such a check has passed.

### 1.3. Recovery

With L the stream's length and n(p, z) the position after a record of z
bytes at p, meta blocks skipped; first the walk, which reads only (028-67,
C1; Frans, 2026-11-27), then the writes:

    p := B.lastTrans, or 128 if −1;  P := p
    walk:                                              (walkTail)
        r := the record bytes from p to the end; if r = 0: go to end
        h := the first min(r, 32) bytes at p
        if r < 4: the record is torn; refuse at P unless it is own;
            the torn record is at p; go to write
        z := h's size
        if z < 5: refuse at P
        if r < z: the record is torn; refuse at P unless it is own;
            the torn record is at p; go to write
        refuse at P unless the last byte is 0 or 10
        if it is the first record and committed: refuse another
            format (a VersioningStreamException)
        if committed: refuse at P unless h holds its check; refuse
            another format (028-70); P := n(p, z)
        if aborted and h holds its check: P := n(p, z)
        p := n(p, z)
    end: refuse at its start if the last record is committed, ended
        at P, and does not parse
    write, held until the start's last check (below):
    if L > 0 and L mod MD < M: append the rest of the block, zero but
        the magic and the version: an invalid block          (005-27);
        all zero if its bytes are zero so far                (028-60)
    the meta block in memory := B, whole, its reserved bytes too
    if a torn record is at p:
        if r < 4: complete the size field: zeros, the first
            of them 1 if zeros give z < 48          (027-03, 7)
        append z − r zeros                          (last byte 0)

The writes are held in memory, not written (028-70, 2026-11-28;
`RecoverableStream.recover(check, true)`): the storage is as it was, and
the start reads the stream, and its length, with them; a run of zeros is
held as its length, a meta block inside the completion as its 128 bytes.
They are written after the start's last check of what it reads,
reclaim's (1.9; `NodeStream.writeRecovery`), the same bytes in the same
order; an append writes them first too. So a start refused by any check
of 1.2 to 1.9 has written nothing. Until 028-70 they were written here,
and a refusal after the walk, by a check of 1.4 to 1.9, came after them.

A torn record is own (028-67; T1 of 031-06's review 3, 2026-11-28) if h
holds its check (r of 32 or more); or if, w the number of its bytes up to
the last that is not zero, at least min(r, 4), w is below 32, its first w
bytes begin a header (if w < 4: the first byte a multiple of 8; else z of
48 or more and a multiple of 8, and if w > 4 the format byte 9), and its
bytes from w to r are zeros (`RecoverableStream.tornRecordIsOwn`; the
zeros after h are read only if h does not hold its check).

"h holds its check": bytes 5 to 7 of the header are the check of the
database id, p and the header's other bytes (027-03, 8.1), the Core's
check (`StoredTrans.RECORD_CHECK`), which the storage layer's recovery
takes as a hook. "Refuse at P": a `BadTailException`, an SFE, before
anything is written, whose message gives the cause, P and the way out
(keep a copy of the files and cut the stream at P); P is the end of the
last record found to be one, or the start of the committed record that
ends there if that record does not parse whole (another file's bytes can
begin inside a record, after its own header). An aborted record whose
header does not hold its check, as a fill after a cut header leaves it,
is walked over and not counted. The walk ends at a meta block too: L
can be at or in the block after a record that ends at its position.

A torn last record becomes an aborted one, which every walk skips. That
is 014-01's contract (section 7; Frans, 2026-11-05): the storage keeps a
prefix of what was appended, a start recovers only a truncated tail, and
other damage is refused as far as the checks see it.

Every later start takes what a start's completion wrote (028-67, T1;
2026-11-28). The completion appends zeros only, after the missing bytes
of a cut size field, and a torn record that is own is the begin of a
header followed by zeros: so the record that a later start finds cut
again, after a kill during the completion, with the completion's zeros
left out by `FileStream`'s open (below), or with a meta block that the
completion wrote inside the record, is own, and its completion appends
the same bytes (but for a meta block that the kill cut, completed as an
invalid block). Until then a torn record was own only if h held its
check or the end of the stream cut it within its 32 bytes (z and the
format byte as far as they went), the completion wrote 4 at byte 4, and
a size field was completed to 17 or more: a start after such a
completion, a stop with no commit between, refused the stream
(`BadTailException`), on a file database after a cut at 1 to 4 bytes of
a record, or up to 24 when the completion crossed a meta block, and on
any storage after a kill during the completion (031-06, review 3, T1).

A tail of zeros within the stream's length, which a kill of the process
during an append left on macOS (031-02, F1), is left out of the stream
before the start reads it, when it is a run of at most 8 MB at the end
of the last file: `FileStream`'s open ends the stream where the run
starts, and its first append truncates the file there (027-14; 028-60,
part 2, 2026-11-26); the recovery above sees a cut tail. A longer run, or one on another storage, is recovered
as a cut where its zeros begin inside the last record: z, read before
them, reaches to or past the end, and the zeros are read only if they
begin in its header (h does not hold its check), to see that they are
zeros; blocks of zeros among them are not valid (1.2, step 3). Zeros
that cover a whole size field at a record's start, where they begin or
past the end of the record they begin in, give z = 0 there: refused,
"Bad transaction size in db stream, 0, spos P. Stream length: L." and
the way out (028-60; since 028-67 the message goes on with P and the
cut, and the refusal comes before the recovery completes a meta block
that the end of the stream cut: it writes nothing). A size field that
the end of the stream cuts, 1 to 3 zero bytes, is completed as any torn
record's and recovered as an aborted record (Codex's review of 028-60,
2026-11-25).

Another file's bytes in the last file within its length, which a kill
during an append can leave on APFS (035-02), are refused in the same
way, before anything is written: their meta blocks are not valid (1.2,
step 3), and their records do not hold the check of this database's id
at their position; a size read from them no longer makes the recovery
append up to 2 GB of zeros first (035-02, section 10.2). Such bytes inside
the last record, which the end of the stream cuts, after a header that
holds its check, are not read: the record is completed and aborted.

### 1.4. The startup pos and the section

    s := 0;  last := none
    for each record R from B.lastTrans (128 if −1) to the end:
        refuse R's header unless its size is above 16 and at most the
            record limit, its last byte is 0 or 10, and, if 10, its
            format byte is 9 (else a VersioningStreamException)
        the first R must be committed; skip R if not committed
        parse R whole, its header's check too        (028-67)
        refuse unless 0 <= R.startupPos < R's position, a multiple
            of 8, and 0 or at least 128     (015-75; R's own position,
            which the take never writes, since 028-09)
        s := R.startupPos;  last := R's position
    the meta block in memory: lastTrans := last
    section := every committed record from s (128 if 0) to the end,
        parsed; the record at s must be committed          (005-28)
    the clock's last time := the last record's time

sd is read at the end of the start (1.9), from its KV. Until 028-15 it
was B's: `setStartupDistance` set it in the meta block in memory and
wrote a record of at least MD bytes (the dummy `/#i/-dummy`), with a
meta block inside, so that a crash after that block and before the
record's end took the new sd though the record was aborted (028-08, not
a bug). Since 028-15 the setting is a KV of the setter's record: a crash
before the record's end starts with the old sd, one after it with the
new (`testCrashInsideSetStartupDistance`). Until 028-09, a startupPos equal
to its own record's position was taken: a section of R(k) alone, whose
transaction is not rerun, so every key that no index node of R(k) held
was gone, and the next commit wrote that s again
(`testOwnPositionStartupPosRefused`). A start takes s and sd from the
stream only (`Db.readStartupPos`, `Db.readStartupDistanceKv`): `Db.start()` has no
parameters. Until 028-10 (2026-11-14), the public `Db.start(StartParams)`
took a caller's s and sd unchecked and skipped the walk above; an s
after the stream's lost the keys before it for good, a bug by R5.

The record format is 9 since 031-06 (2026-11-27;
`StoredTrans.RECORD_FORMAT`; 027-03, section 8.2): release 2026.7 does not open a database of release
2026.6 (Frans, 2026-11-27), and there is no upgrade path. A database of
2026.6 has meta blocks of version 155 and is refused by its first block
(1.2, step 3) before a record is read. A committed record of another
format under a block of version 156 is refused by the walk before
anything is written (1.3: the format if it is the first record walked
or its header holds its check, since 028-70, else the header's check,
which covers the format byte), and here; for
format 8 the message names release 2026.6 and says that release 2026.6
still opens it (`StoredTrans.formatRefused`;
`NodeStreamTester.testStartRefusesFormat8`).

Then the section is validated (005-75), with or without `-ea`: record
positions at least 128 and strictly increasing; times from 0 to 2^56 − 1
and strictly increasing; each node's position valid; each key node valid
at ts (a klong at least, its sizes, its last time index, its times
strictly increasing, and its key pointers' positions valid, −1 allowed
only after ts). A violation is an SFE.

### 1.5. The section's nodes

A section of one record at 128 is a new database: its top node and key
node become canonical, linked. Otherwise:

1. **The maps.** newById: the id of each index node with a version in
   R(s), ..., R(k) to the position of its newest version there, top
   nodes included. posToId: the position of every index node version
   there, and the prevPos each names, to the node's id. posMap: the
   newest version of each index node, but not one made after ts (a top
   node whose root time, a key node whose first time, is after ts), and
   the value and delete nodes of R(s).
2. **Rule R where the id is known without a read**: a pointer of a
   posMap node whose position is a vpos (its id) or in posToId moves to
   newById's position, if that is newer. The others get Rule R at their
   first follow (part 8) or at the writer's resolve.
3. **The cut back**: every key node version of the section loses its
   klongs after ts. Then no stream pointer of a posMap node (of a key
   node, its key klongs) may be −1 or a vpos: else an SFE.
4. **Memory pointers** between posMap nodes, by exact position, each
   pointee of its pointer's type (019-32). The posMap nodes become
   canonical. A copy of newById, with s and ts, goes to the node
   collection as Rule R for the process's life; until the start ends, a
   key node version read through a pointer is validated, one of the
   section cut back to ts, and one from before the section must have no
   time after ts (021-12).

### 1.6. The super root

    p := R(k).topPos; refuse −1 or a vpos
    id := posToId[p], or the id in the node header at p
    refuse if newById[id] exists and is not p           (015-75)
    x := posMap's node at p, or id's canonical object, or the version
         at p made canonical; refuse it if not a top node
    refuse unless x is the super root at ts that x's skip pointers give

The newest written top node is the super root at ts: a top node is
written only after the startup pos has reached the transaction that made
it (011-11, section 8.3). Until format 5 (2026-10-15) the start looked
for the newest top node in the section, which need not hold one (011-11,
M18). x is the tree's root.

### 1.7. The rerun and D

For each j from s + 1 to k, in order:

1. **The puts.** The value and delete nodes of R(j), in stored order
   (key order, strictly increasing, else an SFE), are given at T(j)'s
   time to the writer as one batch (`Dag.putKvs`, PE since record format
   8, 026-25; part 4), which makes each node it reaches canonical. A node
   made gets the next vpos as its id; if R(j) holds a node with that id,
   its position (a value its offset, 005-34); an index node with a version
   in the section, newById's position. (Until format 8 each KV was put
   alone, and a key node made and taken back was dropped, 023-05, P4.)
2. **D.** For each pair (id, p) of gd(j): id's canonical object; or the
   version at newById[id], or at p if p is a position, whose id must be
   id (015-75), a key node validated and cut back to ts. It is made
   canonical and dirty and joins T(j)'s got-dirty nodes. None: an SFE.
3. **The take's state.** T(j)'s time, position, startupPos, last
   position and own bytes (its values' bytes and 48; 005-49) join the
   take's queue (part 6).

D is rebuilt from the stored ids, not from the rerun's marks: a reclaim
step's touch is not stored and not rerun, and a node that Rule A kept
dirty got dirty in the record that wrote it (`DbStarter.canonicalNode`'s
Javadoc; 024-07). The node table's resident bytes are then counted again
(019-21).

### 1.8. Rule 4, by position

    byPos := the live handle of each canonical object, by its position
    for each node x of D, each pointer i of x to an index node that holds
            no handle and names p (not −1):
        skip if p is a position below the stream's first position (M33)
        id := p if a vpos, else posToId[p], if there
        h := id's live handle if id is known, else byPos[p]
        if no h, no id and x is a top node: h := the live handle of
            the id in the header at p (a read)
        if h holds a canonical object: refuse it if not of the type
            the pointer names (021-11); pointer i := h

Since 005-57 rule 4 reads only those headers (top node versions have no
prevPos, 011-03, G3). Why the maps suffice (005-57's report, section 2):
every write of a node after the version that a node of D names is in the
section, so such a pointer names a vpos, a position in posToId or the
canonical object's own. Argued for Java; proved for the model (section
5). With `-ea` each pointer is also linked by node id, with a header
read (`checkLinkById`): a difference is an `AssertionError`, but an SFE
where only the id finds a canonical object (a damaged prevPos,
2026-11-10) or the type differs.

### 1.9. The end of a start

Every value node in memory has a position and every key node passes its
check (`postStartupCheck`, always on; an `AssertionError` otherwise);
the cut back ends (M22); Rule R stays. The STM's first time is the last
record's (after the validation, 005-75); the database is active; sd is
read from its KV (`Db.readStartupDistanceKv`, 028-15: 4 bytes, 10 to
10^9, else an `InternalDataException`; no KV is an SFE unless this start
created the stream, when the default sd, 50 MB, is kept); reclaim reads
its settings, its table and its current row, and takes a, the position
of the application's last record, off the stream's last record R(k):
R(k)'s position, unless R(k) is reclaim's own, a record that holds a key
of reclaim's that is not a copy (the witness), whose rows hold a as it
was after R(k) (031-06, section 2, rule 6; 031-04, R3). It refuses a
stream whose first position is after the newest cut (fp, 0 if none;
1.10), and makes a cut that a crash or a power loss left pending
(027-13, section 1.9; 028-66); it writes nothing. Then recovery's
writes, held since 1.3, are written (`NodeStream.writeRecovery`;
028-70): every refusal of what the start reads comes before them. Then
`created.txt` is written if missing (015-01; after reclaim's refusal
since 2026-11-27, 028-66's review, R2: before, a start so refused wrote
a missing `created.txt` first); eviction takes in what the start made
resident (015-68, 019-47). The creating start writes the creation's
second record now: an internal transaction with no maintenance
(`Trans.noMaintenance`; 031-06, section 2, rule 11) that puts the
default sd, 50 MB (`Db.DEFAULT_STARTUP_DISTANCE`), at the KV, the
writer's first (027-03, section 14.2; the builder's sd until 028-13,
when `DbBuilder.startupDistance` was removed: another sd is set by
`Db.setStartupDistance` after the start); with `created.txt` both
records are synced, and `created.txt` written, before the start returns
(028-17, 028-18). A crash before that leaves a stream that the next
start refuses (1.2, step 2); from 028-15 to 028-18 such a start wrote
the record itself, with its own builder's sd. The start returns s as
stored, sd, ts, the records read and R(k)'s last position (`StartInfo`).
A start that throws closes the storage before the exception leaves
(005-32).

### 1.10. A start after a cut

Reclaim cuts at pCut only when the record that the last valid meta block
names is at or after pCut and the startup pos at or after pSafe (027-13,
section 1.6). So recovery and the section are after the cut, and blocks
below the first position are not searched. A pointer below the first
position names a version dead for every lookup time from fa on: rule 4
and the writer's resolve leave it (M33); a read that meets it is
027-13's, section 1.8.

A start reads nothing before the newest cut fp that the table records:
the last valid meta block names a record at or after it, the startup pos
is at or after it, and every node and value of the latest state is
stored at or after it (028-66, section 5.2; argued from Reclaim's class
comment, and checked by the restarts on `CutStream`, which refuses a read
below its cut). So the storage's first position may be before fp, as
after a crash between the table and the cut, or a power loss that left a
gap in `FileStream`'s files (027-14); the start then cuts at fp, which
deletes what the storage holds before it, the files before a gap once
1.2's step 6 has passed. A first position after fp means that the stream
lacks bytes of the database (a file removed by hand, a copy that missed
files): `Reclaim.initFromDb` refuses the start (a `StreamIoException`
whose cause, a `ReadBelowFirstPosException`, names the first position,
the cut and the storage's account), and a read below the first position
during a start is refused the same way (`Db.refusalOfMissingBytes`);
nothing is deleted (028-66, 2026-11-27; before, the start went on, and
reads of those bytes failed the database later).

### 1.11. Level 1

Level 1 is a start with sd larger than the stream. The take since 005-49
(`TransSeq.take`, `shareFp`; part 6) takes a share of D in proportion to
S / sd, S the section's length, with a dither, so a record takes the
oldest transaction now and then also while S is below sd: the startup
pos moves and index nodes are written, rarely while the stream is small,
and a start replays nearly the whole stream, not all of it. Argued from
the code. `levels.md`, section 4 (a snapshot), still says "the startup
pos never moves"; `level1.sh`'s header said "startup always replays the
whole stream" until 028-11.


## 2. State

* **During a start**: the section's records as parsed, newById, posToId,
  posMap and byPos; garbage when it returns.
* **For the process's life**: Rule R, a copy of newById with s and ts,
  one entry for each index node of the section, never released; the
  canonical objects of the section, of D and of what the rerun reached;
  the take's queue of T(s+1), ..., T(k) with their got-dirty nodes; the
  meta block in memory, its lastTrans at R(k), so that the next block is
  the one a run without the restart writes; the clock's last time and
  the STM's first time; reclaim's settings, rows, a and first available
  position and time, as the running database had them after R(k) (1.9;
  027-13, section 2).
* **In the stream**: 027-03's meta blocks (section 6), frame and fill
  (7), startupPos, topPos and got-dirty pairs (8.1), prevPos (11) and
  references (14.1).


## 3. Invariants

* **T1, INV-CRASH** and **T2, INV-RESTART** (011-01; part 6): a start
  from a run's stream, or a crash's prefix of whole records, gives the
  run's P and D; restarts change no record. Proved in the model (section
  5). Gated: CrashTest, CorruptStreamTester's truncations,
  `testCrash8InCreation`, PowerLossTest (T1); RestartInvariance, the
  stream byte for byte, `testLevel2SameStreamWithRestarts` (T2).
* **A restart or a stop changes no byte** (since 031-06, 2026-11-27):
  every record is decided by the stream before it and its action, and a
  start's memory of what decides the next record, reclaim's settings,
  rows, a and first available position and time among it, is the running
  database's after R(k) (031-06, section 2, rules 3 and 6). Checked, not
  gated: 031-06's probes, a crash, a failure before `apply` and a stop at
  every record boundary of 23 runs, 27,741 interruptions, each continued
  to the uninterrupted stream, with the start's memory the running
  database's at each, and 570 torn records continued the same (031-06's
  landing, step 3, after review 3).
* **INV-1** (`sis-model.md`, section 8): each node at most once in D;
  the D rebuilt is the run's: proved (`T1_recovery`).
* **Rule R is safe** (lemma M): a newer version serves every time an
  older one serves: proved (`LM_newer`, `LM_ruleR`, `LM_cutTo`).
* **Rule 4 by position is rule 4 by node id**: proved for the model
  (`Rule4Pos_handles`; after a safe cut `Rule4PosCut_handles`, proved at
  the tag `proofs-2026-11-17`, 030-18); tested
  in Java with `-ea` at every start of every test (005-57).
* **The newest written top node is the super root at ts**: argued
  (011-11, section 8.3); refused otherwise (1.6); gated for an older
  topPos (`testOlderTopPosRefused`).
* **A refused start writes nothing** (R1): gated for the magic, the
  version, the node size and an incomplete creation
  (`testRecoverUnreadableWritesNothing`,
  `testRecoverOtherVersionWritesNothing`, `testOtherNodeSizeRefused`,
  `testIsIncompleteCreation`); since 028-67 for the walk's refusals, a
  tail that is not the stream's records and another record format
  (`DbTesterTail`, `NodeStreamTester.testStartRefusesFormat8`); since
  028-66 for the files before a gap that are not the database's and a
  stream whose first position is after its cut, which also delete
  nothing (`FileStreamPowerLossTester`, the files compared byte for byte;
  027-14); since 028-70 (2026-11-28) for every refusal, recovery's
  writes held until the start's last check of what it reads (1.3, 1.9):
  of a record, of the section, of the startup distance's KV, of
  reclaim's settings or table and of the first position against the cut
  (`DbTesterTail.testRefusalsAfterTheWalkWriteNothing` and
  `testOtherFormatRefusedFilesUnchanged`, the files compared byte for
  byte; `RecoverableStream`'s `testRecoveryHeld`; CorruptStreamTester
  fails a refused start that has written). Until then such a start
  first completed a torn tail (027-03, G18).


## 4. Costs and bounds

T3 and T4 are part 6's; what they give a start:

* **The records read in order**, R(s), ..., R(k): less than R(s) + 2 sd
  + R(k): proved for the model's take (`T3_take_reads`, BergDB's take
  since 007-08); Java's take gives the model's on 300 cases: checked
  (TakeCheck). Left out: the record limit and the meta blocks. The
  search for s also parses the record B names and those after it: less
  than MD after B (2 MD after a crash in a block), plus the record over
  B, up to the record limit: argued. Since 028-67 recovery's walk (1.3)
  reads those records' headers first and parses the last committed one
  whole, which the search for s parses again: a start of a file database
  whose last record is 106.6 MB, in a stream of 523 MB, took 4.8 to 5.0 s
  on F53: measured (031-06's landing, step 2, the timing run of
  2026-11-28, `bigtail.sh`).
* **The transactions rerun**: fewer than 2 sd / 48 + 1, T(k) included:
  proved for records of at least m bytes (`T3_take_rerun`), and every
  Java record has at least 48 (`TransSeq.ownBytes`).
* **R(s) and R(k)**: each within its transaction and the debt before it:
  proved, nothing assumed (`T4_ends`, at the tag `proofs-2026-11-17`; 030-18). R(s) can be large: after one or
  two transactions of 1.88 GB each start took 27 to 75 s, 0.6 s once
  150 MB more was written: measured (020-24-13, U13-7).
* **D**: at most the section's got-dirty pairs, 16 bytes each (007-01,
  section 2): argued.
* **A cold start's reads** (007-03, step 6), the versions read at
  random: at most the section's index nodes (in order), and for each
  T(j) its writer's paths and gd(j), + 2; the nodes the rerun makes count,
  unread. Proved from any stream (`coldReads_lazy`; `coldReads_handles`,
  both rules 4). After a run, `coldReads_run` and, with TREE,
  `coldReads_tree` (H + 1 for each node T(j) makes, gives an entry,
  touches or makes unreachable; H the root's level) add |D|. **Without
  |D|** (aec08247): with BergDB's test, TREE and `LiveAppend`, every node
  of gd(j) has a canonical object when the rerun of T(j) reaches it:
  proved (`coldReads_run_noD`, `coldReads_tree_noD`), so 007-03's
  "without T4" holds for the model. **Without the unreachable nodes**:
  with `DropStep` (a split's new nodes take the replaced node's
  children), at most as many as the change's entries (`removedAt_bound`),
  so (H + 1)(new nodes + 2 entries + touched nodes) + new nodes for each
  T(j): proved (`coldReads_tree_drop`). For Java: reduced to `DropStep`,
  not checked on Java's runs (TREE and `RunOK` are, by C-A; `LiveAppend`
  is proved for the trace's instance); what the model leaves uncounted
  is open (section 5). These proofs of a cold start's reads
  (`coldReads_*`, `removedAt_bound`) and their definitions are at
  the tag `proofs-2026-11-17` since 2026-11-18 (030-18); `lean/` no longer holds them.
* **Time, warm** (F53): 7.4 s at 10M keys, 8-byte values and 50 MB, 12.4
  s at 200 MB, 70 to 86 s at 1000 MB with 10M to 50M keys, most of it
  the rerun and the section's nodes: measured (007-05); 6.6 and 12.1 s
  at 50 and 200 MB with rule 4 by position (005-57). Proposed: at most
  0.1 s a MB of sd (024-05, BD6).
* **Time, cold** (s1): 46 and 51 s at 10M keys, 50 and 200 MB, with rule
  4 by position, 34 s of the 46 the rerun's loads; 214 and 210 s before:
  measured (005-57). No bound proposed (BD6). Not measured since format
  7, whose merges read siblings (024-11, TU9), nor since format 8, whose
  joins do too (part 4; 026-25).
* **Heap**: the section's records and the maps, outside the cache
  budget: the live heap peaked at 3.3 to 4.9 sd, D included, 0.9 to 2.1
  times the section above the running database's: measured (019-45).
  Proposed: at most 5 sd above it (BD6).


## 5. In the model

* **Definitions** (trusted): lean/SIS/Startup.lean (`follow`, Rule R;
  `startVersion`, `baseStruct`, `rerun`, `startup`); Phys.lean
  (`Version.cutTo`, `canonOfVersion`, `sectionNodes`, `pathOf`,
  `lazyStartup`, Java's start step by step); Handle.lean (`HMem.linkD`,
  `HMem.linkDPos`, `inPosToId`, `HMem.byPos`, `HMem.linkDPosFrom`);
  at the tag `proofs-2026-11-17` (030-18), BoundCold.lean (`rerunReach`,
  `removedAt`) and BoundColdDrop.lean (`DropStep`, `DropRunOK`).
* **Proved** (no `sorry` under lean/SIS): T1 (`T1_recovery`, `T1_nodes`,
  `T1_crash`) and T2 (`T2_restart`); T1-L (`T1_lazy`: after Java's lazy
  start, reads and writer follows read P at every time up to k, every
  canonical object with its node's whole history), T2-L (`T2_lazy`), CC
  (`CC_canonical`), lemma M; rule 4 by position (005-58:
  `Rule4_positions`, `Rule4Pos_handles`, `RunPos_handles`; after a cut,
  005-62: `Rule4PosCut_handles`, `RunPosCut_handles`); T8
  (`T8_recoverCut`: a start from a safely cut stream gives the same
  lookups from fa on and the same D); the costs of section 4. Since
  2026-11-18 (030-18) rule 4 by position after a cut, `T4_ends` and a
  cold start's reads, statements and proofs, are at the tag
  `proofs-2026-11-17` only.
* **Assumptions**: `RunOK` (A2 to A5); BergDB's still-dirty test, or the
  exact one with a written root (the `_noD` and `_drop` bounds: BergDB's
  only); `LiveAppend` and `TreeRunOK` for T1-L, T2-L, CC and the `_noD`
  bounds; `EvictRunOK` with handles; `ExecRootOK` and `VirtLiveOK` after
  a cut; `DropRunOK` for `coldReads_tree_drop`, needed:
  SIS/BoundColdDropExample.lean (at the tag `proofs-2026-11-17`) has a run that meets the rest and TREE
  where one entry makes six nodes unreachable. A crash keeps a prefix of
  whole records. **Stated, not proved**: nothing.
* **Left out**: bytes and positions (s is `lastSp`, a record number);
  the meta blocks, recovery, the walk that finds s; the checks, refusals
  and formats; R(s)'s values linked at the start; the end's check; heap
  and time; concurrency.
* **Open**, what the model does not cover of Java's start:
  * Header reads, not counted by `coldReads_*`: at the first follow of a
    stream pointer, for the node's id, before the version
    (`followStreamPointer`, step 1); for a top node's pointer that
    neither map of rule 4 finds (005-57 found none); at topPos when not
    in posToId (1.6).
  * Joins: PE's rebalance (format 8; a merge of format 7, 024-21) reads
    a sibling of a changed child with fewer than m entries, for its live
    count (M1's choice of the left or the right neighbour), and may leave
    it unchanged when it joins the other one; such a sibling is on no
    path of `pathOf`, so the cold-read bounds do not cover Java's rerun
    of the transactions that join, deletes mostly.
  * The touch: Java's rerun does not repeat a reclaim step's touch
    (1.7), the model's does; that D adds no read (`MemInv.coverGd`)
    rests for Java on the touched nodes being on the step's put paths
    (`canonicalNode`'s Javadoc): argued.
  * Rule R's time: the model applies it to every stream slot it makes
    (`canonOfVersion`), Java to some at once and to the rest at their
    first follow; argued the same (Rule R twice gives what it gives
    once) and checked by C-L, with no theorem.
* **Conformance** (027-02; TraceCheck.lean): C-L, every first touch
  after a restart against the model's rule (`firstFailures`); the trace
  checker on runs with restarts (`level2.sh`, step 7); rule 4 by
  position against by node id after cuts (`checkHandleCut`,
  `posCutCounts`, SIS/ReclaimExample.lean).


## 6. In Java

`core/Db` (`startInner`, the order of 1.2 to 1.9, and the methods it
calls, `readStartupPos` and `readStartupDistanceKv` among them;
`StartInfo`);
`core/DbStarter` (1.4's validation to 1.9); `core/NodeCollection`
(`setStartupSection`, `readVersion`,
`endReconstruction`, `followStreamPointer`, `resolvePointers`,
`linkToCanonical`, `checkLinkById`); `NodeStream.TransIterator`,
`readRecordHeader`; `TransSeq.TransInfo`, `ownBytes`; `KeyNode`
(`toPreviousState`, `validateStreamNode`); `TopDs.findSuperRootAtTime`;
`Reclaim.initFromDb` (a, `isOwnRecord`; the first position against the
cut, `StreamAfterCutException`); `Db.refusalOfMissingBytes`;
`storage/RecoverableStream` (`recover` and its helpers, `walkTail`,
`tornRecordIsOwn`, `checkLastTransSpos`, `checkLeftovers`,
`leftoverProblem`, `isIncompleteCreation`, `writeRecovery` and `Hold`,
the writes held; `NodeStream.writeRecovery`), `RecoverableStream.RecordCheck`
and the Core's, `StoredTrans.RECORD_CHECK` (`headerCheck`,
`formatRefused`), `BadTailException` and `MetaBlock` (`isOwn`); the
storage's `AppendOnlyStream.checkLeftovers`, `FileStream`'s. The Pub API:
`Database.getStartupInfo()`. The C clone (012, 022): `starter.c`,
`recover.c`, `meta.c`, `ncoll.c`, without the prevPos refusal and the
cycle check (027-03, 14.2).


## 7. Tests

* **Gated by `before-commit.sh`** (the counts of 2026-11-28):
  `DbTesterRestart` (46, 6 of them f;
  the refusals of corrupt times, startupPos, got-dirty ids, an older
  topPos, a meta block's lastTrans, another or no node size; a crash
  inside `setStartupDistance` and a startupPos at its own record, 028-08
  and 028-09);
  `DbStarter` (7); `RecoverableStream` (45: crashes in a header, a record
  and a meta block, the fill, an incomplete creation, refusals that
  write nothing, `testLeftoverProblem`, the writes held,
  `testRecoveryHeld`); `MetaBlock` (5, its own position
  and id among them); `NodeCollection`'s `testFollowRuleR`
  and five `testLinkToCanonical*`; `DbTester.testCrash8InCreation`;
  CorruptStreamTester's sample and seven `testFound*`; rule 4's `-ea`
  check at every start; `DbTesterTail` (10 of its 13, 2 of them f; 028-67:
  stale tails, zeros, another database's bytes and an older stream file's,
  each started or refused before a write and started after the cut at P;
  T1's `testCompletionTakenLater` and `testCompletionTakenLaterFiles`, the
  stream after a start's completion cut, and zeroed, as a kill during it
  leaves it, each started, and its completion the first start's byte for
  byte; its f-tests on every 512 bytes and on a file database's last
  file; 028-70's `testRefusalsAfterTheWalkWriteNothing` and
  `testOtherFormatRefusedFilesUnchanged`, refusals after the walk with a
  torn record after them, the stream and the files byte for byte as
  before); `StoredTrans`'s `testHeaderCheck` and `testRecordCheck`;
  `NodeStreamTester.testStartRefusesFormat8` (031-06); the gap's tests of
  027-14 (028-66), `PubTesterJavadocNewUsers.testStartWithTheFirstFileDeleted`
  among them.
* **In the night**: `level2.sh` (RestartStress, RestartInvariance,
  CrashTest, C-L); `level3.sh` (with reclaim; PowerLossTest);
  `level4.sh` (with eviction); CorruptStreamTester's full set;
  `DbTesterTail`'s three night tests (every cut of a completion, a long
  run of zeros in a header); `kill-restart.sh`. By hand:
  `performance.sh`'s restarts; StartupBench; 031-06's probes of the
  interruptions at every record boundary (`P2CrashProbe`, section 3).


## 8. Principles and rules

**P5**, bounded startup: the section by T3, its ends by T4, a cold
start's reads by `coldReads_*` (for Java reduced to `DropStep`; at
the tag `proofs-2026-11-17`); the
time measured, with no constant. **P2**: a restart changes no record
(T2); the meta block in memory is set as the run without the restart
has it; since 031-06 a stop changes no byte either, and a start reads
reclaim's state off the stream and writes nothing for it (1.9; section
3). **P10**: sd is the start's one setting, in the stream. **P7**: a
stream that breaks a check is refused with an SFE; damage the checks
miss may fail a read later (014-01, section 7, point 3); a tail that is
not the stream's records is refused before anything is written, with P
and the way out (028-67). **R1**: a refused start writes nothing,
recovery's fill included since 028-70 (G18). **R5**: a start
takes s and sd from the stream only; no parameter gives them (1.4;
028-10). **P12**: keys and values are
bytes. **P1** is about a running database; a start holds both locks,
and P5 bounds it.


## 9. Limits and open work

* T4's debt for BergDB's test is bounded only with at most Q pointer
  parents a node (`T4_debt_java_tree`; part 6); a cold start's reads no
  longer depend on it.
* `DropStep` is not checked on Java's traces, as C-A checks TREE: open.
  Its words are those of format 7's writer (a split's new nodes); since
  format 8 the writer is PE (part 4), whose cuts, joins and collapses
  were not examined against it (026-25 did not touch these proofs, which
  are at the tag `proofs-2026-11-17`).
* A cold start in seconds needs the rerun's reads cheaper or fewer
  (007-05, point 3); after it the writer reads a header for each stream
  pointer of D's nodes it writes, 1.48 million in 300 transactions at
  50 MB (005-57, finding 3; its part 2, not made).
* Refusals that depend on `-ea` (027-03, G14, J3); s not shown to be the
  take's (G12, 015-73); sd not range-checked (G9). Fast restart (006-06)
  is an idea; the start's heap could be halved (019-45, for 017-07).

**Found while writing, to fix (028 entries)**:

* 028-08: a crash inside `setStartupDistance`'s record, after the meta
  block in it, starts with the new sd though the call never returned
  (1.4). Evaluated: not a bug (2026-11-13).
* 028-09: `checkStartupPos` took a startupPos equal to its own record's
  position (1.4). A bug, fixed (2026-11-13): refused.
* 028-10: the public `Db.start(StartParams)` took a caller's s and sd
  unchecked (1.4). Evaluated: a bug by R5 (2026-11-13). Fixed
  (2026-11-14): the parameters removed (option A).
* 028-11: 027-03:415, :1116, :1234: the creation as 264 bytes; it is 272
  (`Db.CREATION_LENGTH`, since 024-25). Fixed (2026-11-13).
* 028-11: `java/stress/level1.sh`:2–3, :29–30: "startup always replays the whole
  stream"; since 005-49 the startup pos moves also below sd (1.11). Fixed
  (2026-11-13).
* 028-11: 010-01, 01-principles.md:357, P5: T3 "not yet" for BergDB's own take;
  `T3_take` proves it since 007-08. Frans edits 010-01: the sentence is
  proposed in 028-11.
* 028-11: 019-45:56: "the maps are garbage when the start returns"; Rule R's
  copy of newById stays (section 2). A dated note in 019-45 (2026-11-13).
* 028-11: `NodeCollection.linkToCanonical`'s Javadoc named only an
  `AssertionError` (comment 10). Fixed (2026-11-13).


## 10. Evidence

001-08 (M22, M33, M44); 005-27, 005-28, 005-32, 005-33, 005-40 (recovery
and refusals); 005-49 (own bytes); 005-50 (node size); 005-57 (rule 4 by
position; cold 46 s); 005-58, 005-62 (its theorems); 005-75 (the
validation); 007-01, 007-03 (step 6), 007-05 (warm and cold), 007-08
(`T3_take`), 007 at aec08247 (`coldReads_*_noD`, `DropStep`); 011-03
(G3); 011-11 (8.3, M18); 014-01 (section 7); 015-01; 015-68, 019-47;
015-73, 015-75; 019-21; 019-32, 021-11; 019-34; 019-45 (the heap);
020-24-13 (U13-7); 020-28; 021-12; 024-05 (BD6); 024-21, 024-25 (format
7); 026-08; 027-03 (sections 6 to 8, 14); 028-60 (a tail of zeros);
028-66 (the gap, the files before it, a stream that lacks bytes); 028-67
(C1, C3, T1); 031-04 (R3, a); 031-06 (section 2, rules 1, 3, 6 and 11;
record format 9; the sweep); 035-02 (another file's bytes after a kill).


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-13. The draft, by an agent of coord-1113, from the code at
5dc6cd29, the Lean files and the items of section 10 (027-04, section
5.2). For a second agent's review against the code.

2026-11-13. Reviewed against the code at c82bce56 and the Lean files by
a second agent of coord-1113 (027-04, section 5.2): 1.2 (B's time), 1.4
(the walk's header checks; the first record committed; the key node's
pointer check), 1.5 (R(s)'s delete nodes; every key node read
validated), 1.8 (the SFEs of the `-ea` check), 1.9 and section 4 (the
search for s, the record over B) fixed; aec08247's `coldReads_run_noD`,
`coldReads_tree_noD`, `removedAt_bound` and `coldReads_tree_drop` added
(sections 4 and 5): no |D| term, the draft's Q6. By Frans's rule of
13:01 ("The document should document how the algorithms work today"),
no questions: the draft's Q1, Q2, Q3, Q7, Q8 and Q11 are facts of the
code (1.2, 1.4, 1.11, section 2), Q4, Q5 and Q9 open claims of section
5, with the touch the rerun leaves out; what to fix is a list in section
9, with Q10. Comment 2 corrected, comment 10 added. T1 to T4 cut to what
a start uses (part 6 owns them).

2026-11-13. The comments, items 1 to 9, fixed in Java (58dfbfb2); item 10
is 028-11.

2026-11-13. 028-08 to 028-11 by an agent of coord-1113: 1.4 says what
the three tests show (028-08 not a bug; 028-09 fixed, a startupPos at its
own record refused; 028-10 a bug by R5, for Frans), section 7 their
tests, section 9 the outcomes, 1.11 `level1.sh`'s corrected header.

2026-11-18. 028-15 (agent sdkv of coord-1118): sd is a KV read at the end
of a start (1.1, 1.4, 1.9); meta version 155, a block without the node
size damaged (1.2); the creating start's record of sd (1.9).

2026-11-19. Brought up to date with PE (026-25), from the code at
`b03dcea7`: section 4's cold time and section 5's joins (PE's
rebalance reads a sibling for M1), section 9's `DropStep` against PE;
1.7's batch was 026-25's. By an agent of coord-1118, on the branch
`027-pe`.

2026-11-19. 028-18, option C (an agent of coord-1118): the primordial
record alone refused as a creation that did not complete (1.2); the
creating start writes the second record and, with `created.txt`, syncs
both before `created.txt` (1.2, 1.9).

2026-11-25. 028-60: a meta block of zero bytes is not valid (1.2, step
3); a cut block whose bytes are zero so far is completed with zeros
(1.3); what recovery does with a tail of zeros (1.3). By an agent of
lead-1125, on the branch `028-60`.

2026-11-26. 028-60, part 2: `FileStream`'s open leaves a tail of zeros
of at most 8 MB at the end of the last file out of the stream before
the start reads it, and its first append cuts them (1.3). By an agent of lead-1126, on the branch `028-60b`.

2026-11-27. 028-67, C1 and C3 (Frans, 2026-11-27): a meta block is valid
only with its own position and the first block's database id (1.2, step
3); the recovery walks the records before it writes, checks each
header's check of the id, its position and its fields, and refuses a
tail that is not the stream's records with the cause, P and the way out
(1.3); the parse checks the header (1.4). By an agent of lead-1127, on
the branch `028-67-c3`.

2026-11-28. 028-67, T1 of 031-06's review 3: a torn record is own if h
holds its check, or if its bytes up to the last that is not zero begin a
header and zeros follow them; the completion writes zeros only after a
cut size field's missing bytes, and completes a size to 48 or more; so
every later start takes what a start's completion wrote (1.3). By an
agent of lead-1127, on the branch `028-67-t1`.

2026-11-28. Brought up to date with 031-06's landing and 028-66's option
C, from the code at 8a0897cf: section 1 (a start has none of reclaim's
work to complete, 031-06); 1.2 (meta block 0's own position; step 3's and
step 5's refusals of a stream that lacks bytes; step 6, the files before
a gap, 028-66); 1.4 (record format 9 and the refusal of 2026.6's
databases, 031-06; the header's format byte 9, not 7); 1.9 (reclaim's a
read off the last record by the witness, 031-06, rule 6; the refusal of a
first position after the cut; `created.txt` after it; the creation's
second record without maintenance); 1.10 (a start reads nothing before
the cut; the gap; the refusals of a stream that lacks bytes); sections 2,
3 (a restart or a stop changes no byte, checked by 031-06's probes; R1 and
the walk's refusals), 4 (the walk's parse of the last record), 6, 7
(the counts of 2026-11-28), 8 and 10. By an agent of lead-1127, on the
branch `031-06-docs`.

2026-11-28. 028-70: recovery's writes are held in memory until the
start's last check of what it reads, reclaim's, so that a start refused
by any check writes nothing (sections 1, 1.3, 1.9, 3, 6, 7 and 8); the
walk refuses every committed record of another format whose header holds
its check (1.3, 1.4); B's time is checked at the search for s (1.2). By
an agent of lead-1127, on the branch `028-70-refuse-first`.
