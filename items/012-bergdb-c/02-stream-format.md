012-02. The stream format of BergDB
===================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg; the document written on 2026-10-28. **Status: done**
(started 2026-10-28 13:47, done 17:05, set by the conductor after the
review): the document is written and checked (Done-when items 1 to 6 hold, item 5 for 012-05's quick and full
sets; 14.6); its review by a second agent (14.3, step 5) was made on
2026-10-28, 16:22 to 17:05 (section 15): 21 findings, 2 of them errors
(reclaim goes on with an iteration in progress when the retain duration
is forever, 8.13; a leaf's key klong never names a delete node, 6.3.1)
and 5 omissions, all fixed in this document; C1 to C4 hold. Approved
with 012-01 by Frans's go (012-01, 9.1).
**Reference:** Java's `main` at `404d2ee` (`java/` last changed at
`fd8f513`). Everything below describes the Java code of that commit, and
a line quoted is quoted from it.
Phase A (012-01, section 8). Effort: max. After: nothing.

This document defines BergDB's stream and its directory as Java writes
them, byte for byte, for a second implementation that reads and writes
the same bytes: the C clone, whose tasks 012-06 to 012-11 are written from
it. The code is the definition (012-01, 3.1). This document says what the
code does, which method writes each field and which checks it, and quotes
the code where it is subtle. It proposes nothing; what looks odd is
described as it is. When 012-10 is done it moves to
`docs/stream-format.md` (012-01, D6b).

Sections 1 to 7 are the format; 8, what decides the bytes a writer
writes; 9, the directory; 10, the determinism audit; 11, the differences
from the text of 2015; 12, the format of `StreamScan`, Java's scanner,
with which every claim here was checked (section 14.6 says how); 13,
questions for Frans; 14, how it was made: the task's plan and progress;
15, the review of the document against the code by a second agent.

**Conventions.** Classes and methods are Java's, in
`java/src/bergdb/` (`core`, `dag`, `storage`, `stream`, `common`). *SFE*
is `bergdb.storage.StreamFormatException`, which `VersioningStreamException`,
`BadMagicBytes` and `StreamChecksumException` extend. Types: `u8`, `u16`,
`i32`, `i64`, little-endian; `i64` and `i32` are two's complement.
*pos* is a stream position, *off* an offset in a record's or a node's
bytes. D = 200,000 and M = 128 are the meta block distance and size,
B = D − M = 199,872.


# 1. The reference and the versions

The stream has five version numbers. Each is checked where it is read,
and a stream with another value is refused: Java reads only what it
writes (new databases only, F1-008-11's Q5). The meta block version is
checked before a start writes anything (005-40); the record and node
formats when a record is parsed, after recovery, whose zero fill uses the
framing only (4.4).

| Number | Value | Defined in | Covers | Written as | Read as |
|---|---|---|---|---|---|
| Meta block version | 154 | `MetaBlock.CURRENT_VERSION` (`VERSION_154`) | the framing: the meta blocks' size, distance and layout; a record's size field and last byte (`RecoverableStream`) | `i32` at meta bytes 4–7 (`MetaBlock.initBlock`: `Bytes.intToBytesLE(CURRENT_VERSION, block, 4)`) | `u16` at bytes 4–5, by `RecoverableStream.readMetaBlock` for every block it reads, valid or not; bytes 6–7 are not read |
| Record format | 5 | `StoredTrans.RECORD_FORMAT` | what a record holds: its 32-byte header with `topPos` (since 2026-10-15), the nodes, the end marker, the got-dirty list | `i32` 5 at record bytes 4–7 (`Serializer.serializeHeader`: `int0 \| (int1 << 32)`) | `u8` at byte 4, bytes 5–7 skipped (`StoredTrans.Parser.parse`) |
| Top node format | 2 | `FORMAT_VERSION` in `StoredTopNode.toLongs` | section 6.2 | `u8` at node byte 5 | `StoredTopNode.parse` |
| Key node format | 2 | `FORMAT_VERSION` in `StoredKeyNode.toLongs` | section 6.3 | `u8` at node byte 5 | `StoredKeyNode.parse` |
| Value node format | 4 | `FORMAT_VERSION` in `StoredValueNode.toBytes`, for values and deletes | section 6.4 | `u8` at node byte 5 | `StoredValueNode.parse` |

Another value gives a `VersioningStreamException` (an SFE): from
`readMetaBlock` ("Cannot read meta block with version"), from the parser
of a record (`StoredTrans.formatRefused`) or of a node ("Cannot parse ...
of format version"). A record is parsed only when the start or a read
needs it, so a record format is checked on the records that the start
reads (section 4.3) and on those read later.

One field has no version of its own: the maximum node size at meta bytes
44–45, added on 2026-10-27 (005-50, `bf19075`) in bytes that were reserved,
so the meta version stayed 154 (`MetaBlock.CURRENT_VERSION`'s comment).
A start refuses a stream whose last valid meta block has 0 there, as every
block written before 005-50 has (`Db.refuseOtherNodeSize`,
`VersioningStreamException`). So Java at the reference starts only
databases created since 2026-10-27.

The paced take (`f89846d`, 2026-10-28, 007-07) changed what Java writes
(every record's choice of index nodes, section 8.7) and no version: a
stream written before it reads as any other, and records written after
it follow the new take.


# 2. Numbers, positions and alignment

## 2.1 Numbers

Every integer is little-endian. Positions, times and ids are `i64`.
`u16` holds the maximum node size and the node checksums. A *pointer*
field, a reference from the stream to the stream (a key node's refs, a
top node's root and skip pointers, `prevPos`, `startupPos`, `topPos`, a
got-dirty position, a meta block's `lastTrans`), is an `i64`: a
position, a vpos (2.5), or −1.

## 2.2 Positions

The stream is a sequence of bytes from position 0. A position (`spos`)
counts every byte, meta blocks included. Reclaim cuts the front of the
stream (section 9.4); positions do not change, and the first position
that can be read, `AppendOnlyStream.getFirstPos()`, is then larger than
0. `Spos.NULL` is −1: none.

## 2.3 Record bytes and positions

A record's *bytes* are its own bytes in order, without the meta blocks
that lie between them in the stream. A record's size, a value node's
stored offset and every offset in a record count record bytes. The
position of record byte `n` of a record at position `start` is
`RecoverableStream.getSpos(start, n)`:

```java
final long startOffset = sposStart % META_BLOCK_DISTANCE;
final long transBytesPerBlock = META_BLOCK_DISTANCE - META_BLOCK_SIZE;
long blockCount = size / transBytesPerBlock;
final long left = size - blockCount * transBytesPerBlock;
if (startOffset + left >= META_BLOCK_DISTANCE) {
    blockCount++;
}
return sposStart + size + blockCount * META_BLOCK_SIZE;
```

With `>=`, a byte that would fall at a multiple of D falls after the
meta block there. `getSpos(start, size)` is the next record's position,
and `getSpos(start, size − 1)` the position of the record's last byte
(`lastPos`). The inverse (005-34), the position of the record whose byte
`n` is at `pos`, is `getStartSpos(pos, n)`: with
`transPos(p) = (p / D) * B + max(0, p % D − M)`, the record bytes before
`p` (`getTransPos`), and `t = transPos(pos) − n`, it is
`(t / B) * D + M + t % B`; it throws `IllegalArgumentException` when
`pos < 0`, `pos` is in a meta block (`pos % D < M`), `t < 0` or `n < 0`.

## 2.4 Alignment

Records start at multiples of 8 (`RecoverableStream.TRANS_ALIGNMENT`,
`NodeStream.TRANS_ALIGNMENT`): the first starts at 128, every record's
size is a multiple of 8 (section 5), and D and M are multiples of 8. The
parser checks it: `tpos % RecoverableStream.TRANS_ALIGNMENT != 0` throws
`IllegalArgumentException` (`StoredTrans.Parser.parse`), and it asserts
that the last byte's position is 7 modulo 8. In a record, the 32-byte
header and the top and key nodes have sizes that are multiples of 8, and
value nodes multiples of 4 (6.4); so a top or key node is at a position
that is a multiple of 8, a value node at a multiple of 4.

## 2.5 Ids and vpos

Every node has an id, an `i64` given when the node is made in memory
(`Db.setIdOfNode`) and stored in every version of it. An id is a *vpos*,
a virtual position: an odd number, which is also the node's position in
memory until the node is first written (`Spos.isVpos(x)` is
`x % 2 == 1`, so −1 is not a vpos; `Spos.nextVpos(v)` is `v + 1` for an
even `v` and `v + 2` for an odd one). The nodes made by a transaction get
the odd numbers from its record's position + 1 up, in the order they are
made (section 8.4). The creation is the exception: its root key node
has the id 0, which is even, and its top node the id 1 (8.2), not 129
and 131.

A written node is at an even position (2.4). So a reference that is odd
names a node that had not been written when the reference was written,
and an even one a version of it. `Spos.newer(pos, ref)` (item 009)
orders the two kinds: a position is newer than a vpos, and between two
positions the larger is newer.

## 2.6 Times

A time is an `i64` in units of 100 ns since 1970-01-01 00:00 UTC
(`Clock.UNITS_PER_SEC` = 10,000,000), from `Klong.MIN_TIME` = 0 to
`Klong.MAX_TIME` = 2^56 − 1. Every time in the stream is a transaction's
time (section 8.1). The records' times increase strictly with their
positions; the start checks it for the records it reads
(`DbStarter.validateTransactions`: "non-increasing tt", an SFE).


# 3. The meta block

A meta block is at every position k · 200,000, k = 0, 1, 2, ..., and is
128 bytes long (`RecoverableStream.META_BLOCK_SIZE`,
`META_BLOCK_DISTANCE`). Its layout (`MetaBlock`, its class comment):

| Off | Size | Type | Field | Meaning and range | Written by | Checked on reading by |
|---|---|---|---|---|---|---|
| 0 | 4 | bytes | magic | `62 65 72 67`, "berg" (`MetaBlock.MAGIC`) | `MetaBlock.initBlock` | `RecoverableStream.readMetaBlock`, for every block it reads: `BadMagicBytes` (an SFE; at a start `Db.startInner` turns it into `BadCryptoKey`); `MetaBlock.checkFormat`, for a valid block |
| 4 | 4 | `i32` | version | 154 (section 1) | `initBlock` | `readMetaBlock` reads bytes 4–5 as `u16`: not 154 gives `VersioningStreamException` |
| 8 | 8 | `i64` | time | the creation's time, that of the record at 128, in every block of the stream | `Db.writePrimordialTransaction` (`meta.setTime(tt)`), the only call of `setTime`; later blocks copy it (below) | `checkFormat`: below 0 is an SFE. Nothing else reads it |
| 16 | 8 | `i64` | `lastTrans` | the position of the last record appended before the block, or −1 if none (only the block at 0, and blocks of a recovery fill, 4.4) | `NodeStream.appendNodes`, after each record (`rstream.getMetaBlock().setLastTransSpos(pos)`); `Db.getStartupPosFromLastTransaction` at a start | `checkFormat`: below 0 and not −1 is an SFE. Read by recovery (4.4), the start (4.3), `getPosOfTransCompletedBefore` and reclaim's cut (8.13) |
| 24 | 16 | bytes | database id | 16 bytes: random (`DatabaseId.createRandom`), or the builder's (`DbBuilder.id`, `testId()`: `7d ee f4 8a 84 66 f3 87 c0 bb 72 9d 2c 8a ab 38`) | `writePrimordialTransaction` (`meta.setId`) | not checked; read only for replicas (`StorageManager`, `DbHelper`) |
| 40 | 4 | `i32` | startup distance | the setting in force, sd: from 10 (`DbBuilder.startupDistance` refuses less) to 2^31 − 1; `setStartupDistance` clamps to 400,000 to 10^9 | the `Db` constructor (the builder's value), `writePrimordialTransaction`, `Db.setStartupDistance` | not checked (audit, doubt D9); a start takes it as the setting in force (`Db.handleStartParams`) |
| 44 | 2 | `u16` | maximum node size | 8, 14, 30 or 62 (`DbBuilder.maxNodeSize8()` to `maxNodeSize62()`) | `writePrimordialTransaction` (`meta.setMaxNodeSize`, 005-50) | `Db.refuseOtherNodeSize`, on the last valid block: 0 gives `VersioningStreamException`, another size than the start's an SFE |
| 46 | 81 | zero | reserved | zero | (a new block is zero) | not checked; copied (below) |
| 127 | 1 | `u8` | last byte | 10: the block is valid | `initBlock` | `MetaBlock.isValid`: another value makes the block invalid |

The blocks are written by `RecoverableStream.writeMetaBlock`, which
appends the 128 bytes of the in-memory `MetaBlock` (`RecoverableStream`'s
field `metaBlock`) as they are at that moment, eagerly: as soon as an
append reaches the block's position (section 4.2). The in-memory block
changes so:

* **At the creation**, `writePrimordialTransaction` sets the id, the
  startup distance, the node size and the time, before the creation's
  record is appended; `lastTrans` is −1 (`initBlock`). The block at 0 is
  written by that append, before the record's first byte.
* **After each record**, `NodeStream.appendNodes` sets `lastTrans` to the
  record's position, after `rstream.append(...)`. So a block written in
  the middle of a record, or right after a record that ends at the block,
  names the record before (seen in the scan of `big`: the block at
  200,000, inside the record at 384, has `lastTrans=264`).
* **`setStartupDistance`** sets the startup distance before it runs its
  dummy transaction, and sets the old value back if the transaction is
  refused (section 8.12).
* **At a start**, recovery copies the last valid block whole, reserved
  bytes included (`metaBlock.setFromOtherMetaBlock(lastBlock)`), and then
  `getStartupPosFromLastTransaction` sets `lastTrans` to the last
  committed record (4.3). The builder's startup distance, which the
  constructor put in the block, is overwritten by the copy: a database
  keeps the startup distance of its stream.

A block is *valid* when its last byte is 10. Java writes every block
whole and valid; an invalid block is one that a crash cut, completed by
recovery's fill with a last byte of 0 (4.4).


# 4. The framing and recovery

## 4.1 The record frame

Between the meta blocks the stream is a sequence of records. The first
is at 128; each next one is at `getSpos(pos, size)` of the one before,
with no gap. The framing layer (`RecoverableStream`) knows two fields of
a record:

* bytes 0–3, `i32`: the record's size in record bytes, its own bytes
  only;
* its last byte, at record byte `size − 1`: 10
  (`RecoverableStream.LAST_BYTE`) for a committed record, 0 for a failed
  one. Java's writer writes committed records only; a failed record is
  made by recovery's fill (4.4).

## 4.2 Appending

`NodeStream.appendNodes` serializes a record whole (section 5) and hands
it to `RecoverableStream.append` in one call, which splits it around the
meta blocks:

```java
int blockPos = (int) (aosSize % META_BLOCK_DISTANCE);
...
int distanceToMeta = META_BLOCK_DISTANCE - blockPos;
if (blockPos == 0) {
    distanceToMeta = 0;   // Special case
}
while (size >= distanceToMeta) {
    aos.append(buffer, offset, distanceToMeta);
    writeMetaBlock();
    size -= distanceToMeta;
    offset += distanceToMeta;
    distanceToMeta = META_BLOCK_DISTANCE - RecoverableStream.META_BLOCK_SIZE;
}
if (size > 0) {
    aos.append(buffer, offset, size);
}
```

So the block at a multiple of D is written as soon as the record bytes
reach it: also when a record ends exactly there (`size >=`), and first,
before any record byte, when the stream's length is at the block's
position, which in Java's writer happens only at position 0, the
creation. A stream that Java has written ends at a multiple of D only
after a crash between the record's last piece and its block (two appends,
005-27). With `useChecks` (always, from `appendNodes`), `append` refuses a
buffer whose last byte is not 10 or whose size field is not its length
(`IllegalArgumentException`), and a stream that ends inside a meta block
(an SFE).

## 4.3 Reading and the start's walk

`RecoverableStream.read` reads record bytes, skipping the meta blocks. A
start reads the stream so (`Db.startInner`, after recovery, 4.4):

1. `Db.getStartupPosFromLastTransaction`: from the record that the last
   valid meta block names (`lastTrans`; 128 if it is −1) to the end of the
   stream, the `startupPos` of the last committed record. The walk is
   `createTransIteratorFromExactStartupPos`: the record at its start must
   be committed, else an SFE (005-28). It also sets the in-memory block's
   `lastTrans` to the last committed record it found.
2. `Db.readTransactions`: from that startup position (0 is read as 128)
   to the end, every committed record, parsed: the startup section, which
   `DbStarter` reruns (section 8.14).

The walk (`NodeStream.TransIterator.next`) reads each record's size and
its bytes; a size below 17 (`16 + 0 + 1`) is an SFE; a last byte that is
neither 0 nor 10 is an SFE ("Bad lastByte"); a record whose last byte is
0 is skipped; the next record is at `getSpos(tpos, size)`.
`RecoverableStream.getPosOfTransCompletedBefore(pos)` gives the record to
walk from to reach a position (the one named by the last valid meta block
at or before it; in a cut stream, by the first valid block after the
first position that names a record at or after it), for the non-exact
iterator.

## 4.4 Recovery

A start recovers the stream before it reads it (`NodeStream.recover`,
`RecoverableStream.recover`; called by `Db.startInner` after the checks
of 4.6):

1. **The last valid meta block.** `readLastValidMetaBlock`: the blocks
   from the last complete one (at or before `length − 128`) down to the
   first one at or after the first position; the first of them that is
   valid. Every block it
   reads, valid or not, must have the magic bytes and version 154 (4.6 and
   section 3). No valid block is an SFE ("Could not find *any* valid meta
   block"). It reads before it writes (005-40).
2. **A cut meta block** (`fixMetaBlockIfNeeded`): if the stream ends inside
   a meta block, or at its position (`length > 0` and
   `length % D < 128`), the rest of the block is appended from
   `MetaBlock.FILL_OUT_TEMPLATE`: "berg", 154 as a `u16` at bytes 4–5, and
   zeros, the last byte 0. The block so completed is invalid: its last
   byte is 0, and it keeps whatever bytes the crash left before the cut.
3. The in-memory block becomes a copy of the last valid block (step 1).
4. **A cut record** (`fixLastTransactionIfNeeded`): from the record that
   block names (128 if none), the records are walked by their sizes. If the
   last one is cut by the end of the stream:
   * if 1 to 4 of its bytes exist, the size field and byte 4 are first
     completed (`transHeaderFixBytes`): the missing size bytes are zero,
     except that the first missing one is 1 when the size read so far
     (missing bytes as 0) is below 17 (`MIN_TRANS_SIZE`); and record byte 4
     is 4 (`TORN_HEADER_FILLER`). With all four size bytes present only byte
     4 is appended;
   * a size below 5 is an SFE ("Bad transaction size");
   * the rest of the record is appended as zeros (`appendZeros`, through
     `append`, which writes the meta blocks it reaches from the in-memory
     block, valid, with the `lastTrans` of the last valid block of step 1).

   The record so completed ends in 0: it is failed, and every walk skips
   it. The size field is the one the crash left (or completed); so the
   fill appends exactly the bytes that the record lacked. A completed
   size is 17 or more (the rule of the 1 above), and a size Java wrote is
   48 or more; only a corrupt size field, with all four bytes present,
   gives 5 to 16: 5 leaves the record whole after byte 4 (its "last
   byte" is the filler 4), 6 to 16 are filled with zeros, and the start's
   walk then refuses either ("Bad transaction size", below 17, 4.3; found
   by 012-06, checked in `fixLastTransactionIfNeeded`,
   `RecoverableStream.java:229-267`).

So after a crash Java writes bytes that a run without the crash does not
have: the failed record, and the meta blocks inside it, whose `lastTrans`
is that of the last valid block before the cut, which can be −1 (the
scan of `recovered-199993`: the record at 199,840, size 1,192, cut at
199,993, is filled to 201,160, and the block at 200,000 is valid with
`lastTrans=-1`, copied from the block at 0). The next record starts after
the failed one. A C port must do the same, byte for byte.

## 4.5 An incomplete creation

A crash while a database is created can leave a part of the creation's
264 bytes (8.2). `RecoverableStream.isIncompleteCreation(264)` (005-33)
recognizes it: the stream is not empty, at most 264 bytes long, its first
position is 0; its bytes begin as `FILL_OUT_TEMPLATE` as far as they go,
for at most 6 bytes (`MetaBlock.beginsAsBlock`: "berg" and 154 as a
`u16`); and then:

* shorter than 128 bytes: yes;
* else the block at 0 must be valid and name no record (`lastTrans` −1),
  else no;
* fewer than 4 record bytes: yes;
* else, with `n` record bytes and the size field `s`: if `n != s`, yes
  exactly when `n < s` (cut); if `n == s`, yes exactly when the last byte
  is 0.

`Db.refuseIncompleteCreation` then throws `DatabaseNotCreatedException`,
and nothing is written (scans `recovered-60`, `recovered-130`,
`recovered-148`: the start refused, the bytes as cut). A stream of fewer
than 128 bytes that is not an incomplete creation (its first bytes are not
"berg" and 154) is refused by the start's first read of a meta block,
`refuseOtherNodeSize` (4.6) through `RecoverableStream.readMetaBlock`: a
`StreamIoException` when it has fewer than 6 bytes, else `BadMagicBytes`
(so `BadCryptoKey`) or a `VersioningStreamException`; nothing is written.
`NodeStream.recover`'s own refusal ("Cannot recover stream without
complete first meta block", an SFE) is not reached from a start (the
review's probe `short`, 15.2, finding 21).

## 4.6 The order of a start's checks

`Db.startInner`: `syncStreams`; `handleEmptyStream` (a stream of length 0
is created, 8.2); `refuseIncompleteCreation` (4.5);
`refuseOtherNodeSize` (section 3; it reads the last valid meta block);
`nodeStream.recover()` (4.4); `handleStartParams` (the startup distance
from the block, the startup position from the last record, 4.3);
`readTransactions`; the clock's last time
(`setLastTransTimeOfDbClock`: the last record's time); `DbStarter`
(section 8.14); `reclaim.initFromDb()` (section 8.13). A `BadMagicBytes`
from the checks or the recovery becomes `BadCryptoKey`.


# 5. The record

A record, at a position that is a multiple of 8 (2.4); offsets in record
bytes:

| Off | Size | Type | Field | Meaning and range | Written by | Checked on reading by |
|---|---|---|---|---|---|---|
| 0 | 4 | `i32` | size | the record's bytes, a multiple of 8, from 48 (no nodes, no got-dirty pairs) to the largest multiple of 8 not above `StoredTrans.recordLimit` (`MAX_RECORD_SIZE` = 2^31 − 9, so 2^31 − 16; `prepareToSerialize` compares the aligned size with the limit) | `Serializer.serializeHeader` (`totalSize` from `prepareToSerialize`) | the walk: below 17 is an SFE (4.3); `Parser.parse`: larger than the buffer is an SFE. The parser does not compare it with the size it parses |
| 4 | 1 | `u8` | format | 5 (section 1) | `serializeHeader` (the `i32` 5 at 4–7) | `Parser.parse`: another value, `VersioningStreamException` |
| 5 | 3 | zero | | the upper bytes of that `i32` | `serializeHeader` | skipped (`offset += 3`) |
| 8 | 8 | `i64` | time | the transaction's time `tt` (section 8.1), 1 to 2^56 − 1 | `serializeHeader` | the start: strictly increasing (2.6). The walk reads it (`transTime`) |
| 16 | 8 | `i64` | `startupPos` | the position of the record that a start reads from, the startup position s: the position of the last transaction that this record's take took, or the startup position before the record if it took none (8.7, 8.9); 0 means the first record (`readTransactions` reads 0 as 128) | `serializeHeader`, from `Db.store` (`x.trans.startupPos = newSp`); 0 in the creation's record | `Db.getStartupPosFromLastTransaction` asserts `>= 0` for each record it walks; a start reads from the last record's (`Db.readTransactions`, an exact walk): the record there must be committed, an SFE else |
| 24 | 8 | `i64` | `topPos` | the position of the latest version of the newest written top node after this record, in this record if written here (8.10); never −1 or a vpos in Java's records | `Serializer.serialize` (`topNode.getSpos()` after `prepareToSerialize`), the node chosen by `Db.store` | `DbStarter.topNodeOfLastTransaction`, of the last record only: a vpos or −1, or a position that does not hold a top node, is an SFE |
| 32 | | | nodes | the top nodes, then the key nodes, then the value and delete nodes, each starting with its size (section 6) | `Serializer.serializeNodes` | `Parser.next`, `NodeStream.bytesToNode` |
| e | 4 | `i32` | end of nodes | 0 | `Serializer.serializeEnd` | `Parser.next`: a node size of 0 ends the nodes |
| e+4 | 4 | `i32` | got-dirty count | N, the number of pairs | `serializeEnd` (`gotDirtyNodes.size()`) | `Parser.parse`: below 0 or above `(buffer.length − offset) / 16` is an SFE |
| e+8 | 16·N | | got-dirty pairs | N pairs (id `i64`, position `i64`): the index nodes that got dirty in this transaction, and the record's nodes still dirty (8.6) | `serializeEnd`: `node.getId()`, `node.getSpos()` | `DbStarter.rerunTransaction`, for the records it reruns: a pair whose node is not found is an SFE ("startup error, node ... not found") |
| | 0–7 | zero | padding | zeros, so that the size is a multiple of 8 | `serializeEnd` (`NodeStream.ZEROS64`, `extraZeros`) | not checked; the parser counts it (`computeZeroCount`) without reading it |
| size − 1 | 1 | `u8` | last byte | 10 | `serializeEnd` (`RecoverableStream.LAST_BYTE`) | the walk (4.3); `RecoverableStream.append` |

The padding comes before the last byte. Its length is
`computeZeroCount(n) = (8 − n % 8) % 8`, where `n` counts the record's
bytes up to and including the last byte (`prepareToSerialize`:
`size += 1` for the last byte, then `extraZeros = computeZeroCount(size)`).
An empty record, as that of a transaction that only deletes a key that
does not exist (8.5), is 32 + 4 + 4 + 1 = 41 bytes and 7 zeros: 48 (the
scan of `n8`, the record at 520).

The parser reads the nodes until a node size of 0 (`Parser.next`; it
also stops when `offset + 4 >= buffer.length`), then the count and the
pairs, and computes `lastPos` from what it parsed:
`getSpos(tpos, parsed + 1 + computeZeroCount(parsed + 1))`, not from the
size field. A node's position is `getSpos(tpos, off)` of its offset. A
record above the limit is refused when it is serialized
(`prepareToSerialize`, a `DbException`), after the transaction's go
point; the checks before it (`Db.checkSize`: the value nodes at most 7/8
of the limit; `Db.checkDirtyNodes`: the index nodes at most 15/16) keep a
transaction from getting there (005-17, 005-31). `StoredTrans.recordLimit`
is `static volatile`; tests lower it.


# 6. The nodes

## 6.1 The node header and the checksum

Every node begins with the same 8 bytes:

| Off | Size | Type | Field | Meaning |
|---|---|---|---|---|
| 0 | 4 | `i32` | size | the node's bytes, these 8 included |
| 4 | 1 | `u8` | type | 10 top node, 20 key node, 30 value node, 40 delete node (`Node.TYPE_TOP_NODE` and so on) |
| 5 | 1 | `u8` | format | 2, 2, 4 and 4 (section 1) |
| 6 | 2 | `u16` | checksum | Fletcher-16 of the node's `size` bytes, bytes 6 and 7 counted as 0 |

The checksum (`NodeChecksum.sum`): `sum1` and `sum2` start at 0; for
each byte `b` (unsigned) in order, `sum1 = (sum1 + b) % 255` and
`sum2 = (sum1 + sum2) % 255`; the result is `sum1 | (sum2 << 8)`, stored
at bytes 6–7, so byte 6 is `sum1` and byte 7 `sum2`. The top and key
nodes compute it over their `long`s with the checksum bytes still zero
(`NodeChecksum.sum(long[], ...)`, the bytes of each `long` least
significant first) and then OR it into the first `long` at bit 48; the
value nodes over their bytes, then write it at 6–7
(`Bytes.ushortToBytesLE`).

On reading, `NodeStream.bytesToNode` checks the checksum first
(`NodeChecksum.sumWithZeroReplace(buffer, offset, size, offset + 6)`,
which counts bytes 6–7 as 0): another value is a
`StreamChecksumException` (an SFE). Then the type: another than 10, 20,
30 or 40 is an SFE ("Bad node type"); then the node's parser.
`NodeStream.readNode`, which reads one node by its position, refuses a
size of 6 or less (an SFE). The parsers do not check the size field
against the node's own layout; the record parser uses it to find the
next node, and refuses no negative size: `Parser.next` moves back by it,
so a crafted record makes it loop until memory runs out; and a record's
and a node's size is allocated before their bytes are read (012-06's
corrupt-input tests, registered as 005-74; Java's writer never writes
such sizes).

## 6.2 The top node

A top node is one link of the chain of top nodes: it points to the
B-tree's root key node of its time and to some older top nodes (the skip
pointers); the newest, the *super root*, is where a lookup starts
(`TopDs`; docs/sis-model.md, 6.3). Its layout, 40 + 16·h bytes
(`StoredTopNode`, its class comment):

| Off | Size | Type | Field | Meaning and range | Written by | Checked on reading by |
|---|---|---|---|---|---|---|
| 0 | 4 | `i32` | size | 40 + 16·h | `StoredTopNode.toLongs` | an assert only |
| 4 | 1 | `u8` | type | 10 | `toLongs` | `bytesToNode` |
| 5 | 1 | `u8` | format | 2 | `toLongs` | `StoredTopNode.parse`: `VersioningStreamException` |
| 6 | 2 | `u16` | checksum | 6.1 | `toLongs` | `bytesToNode` |
| 8 | 1 | `u8` | h | the number of skip pointers: the bit length of the ordinal (`TopNode.height`), 0 to 48 | `toLongs` (`node.pointersLength`) | `parse`: read as a signed byte, below 0 an SFE (005-21); not equal to the ordinal's bit length, an SFE |
| 9 | 1 | zero | | zero | `toLongs` | not checked |
| 10 | 6 | `u48` | ordinal | the top node's number in the chain: 0 for the first, then each new top node one more than the super root before it (`TopDs.newSuperRoot`: `superRoot.topNodeId + 1`, or `DbBuilder.secondTopOrdinal` for the second, 1 by default, a test setting) | `toLongs`: `((long) node.pointersLength) \| (node.topNodeId << (2 * 8))` | `parse`: `bytesToLongLE(buffer, firstOffset + 8) >>> 16`; its test "above `TopNode.MAX_TOP_NODE_ID_VALUE` = 2^48 − 1, an SFE" cannot fail, as 48 bits are read |
| 16 | 8 | `i64` | id | the node's id (2.5); not the ordinal | `toLongs` (`node.getId()`) | read by `NodeStream.readNodeHeader` (`StoredTopNode.ID_OFFSET` = 16) and `parse` |
| 24 | 8 | `i64` | root time | the time at which the root pointer's root became the root: the time of the transaction that made this top node | `toLongs` (`node.rootTime`) | `parse`: outside 0 to 2^56 − 1 an SFE |
| 32 | 8 | `i64` | root pointer | the reference (6.5) to the root key node | `toLongs` (`node.getSerializedRef(0)`) | `parse`: below 0 an SFE |
| 40 + 16·i | 8 | `i64` | skip pointer i | the reference to an older top node, or −1 when unset; set exactly when bit i of the ordinal is | `toLongs` (`getSerializedRef(i + 1)`) | `parse`: set when the bit is clear, or unset when it is set, an SFE |
| 48 + 16·i | 8 | `i64` | skip time i | that top node's root time; −1 when the pointer is unset | `toLongs`: `spos == Spos.NULL ? -1 : node.pointersTime[i]` | not checked; ignored for an unset pointer |

Skip pointer i of a new top node with ordinal `n` (`TopDs.newSuperRoot`):
when bit i of `n` is set, the super root's own skip pointer i if it has
one (its handle and reference, and its time), else the super root itself
(its root time); when the bit is clear, unset. A second new root in the
same transaction does not make a second top node: the super root made by
the transaction gets the new root pointer (`newSuperRoot`, "A second new
space root in the same transaction").

## 6.3 The key node

A key node is a node of one segment's B-tree (section 7): a *segment
leaf* maps a segment's compare values to value nodes (the key's last
segment) or to the root of the next segment's B-tree; an inner node maps
them to its children in the same segment's B-tree. Its content is a
history: an array of klongs, appended in time order, each with a
reference. Layout, 32 + 16·n bytes (`StoredKeyNode`):

| Off | Size | Type | Field | Meaning and range | Written by | Checked on reading by |
|---|---|---|---|---|---|---|
| 0 | 4 | `i32` | size | 32 + 16·n | `StoredKeyNode.toLongs` | not checked |
| 4 | 1 | `u8` | type | 20 | `toLongs` | `bytesToNode` |
| 5 | 1 | `u8` | format | 2 | `toLongs` | `StoredKeyNode.parse`: `VersioningStreamException` |
| 6 | 2 | `u16` | checksum | 6.1 | `toLongs` | `bytesToNode` |
| 8 | 8 | `i64` | `prevPos` | the position of the version this one replaces: the node's position before this write (`prepareToSerialize`: `prevPos[i] = node.spos` before the new position is set); the node's vpos if it was never written; 0 in the creation's root (its id, 8.2) | `toLongs` | `parse`: not a position and not −1 (`Spos.isValidOrNull`) is an SFE. The start uses it to map positions to ids (`DbStarter.createMaps`, `posToId`) |
| 16 | 1 | `u8` | leaf | 1 for a segment leaf, 0 for an inner node | `toLongs` | `parse`: neither 0 nor 1 is an SFE |
| 17 | 2 | `i16` | n | the number of klongs, 1 to the maximum node size (6.3.1, at its end); Java writes `sz << (1 * 8)`, an `int` shift, so bytes 17–19 hold `n` | `toLongs` | `parse`: read as a signed short; below 0 an SFE. A start refuses 0 in the records it reads (`DbStarter.validateTransactions`, `KeyNode.validateStreamNode`: "Key node with size 0", an SFE) |
| 19 | 5 | zero | reserved | zero | `toLongs` | not checked |
| 24 | 8 | `i64` | id | 2.5 | `toLongs` | `readNodeHeader` (`ID_OFFSET` = 24), `parse` |
| 32 + 8·i | 8 | `i64` | klong i | i from 0 to n − 1 (6.3.1) | `toLongs` (`node.klongs`) | not checked by `parse`; `validateStreamNode`'s checks of the time klongs (`checkLastTimeIndex`, `checkIncreasingTime`) cannot fail on parsed bytes (the second never updates its `time`) |
| 32 + 8·n + 8·i | 8 | `i64` | ref i | the reference of klong i (6.5): for a key klong, its child's; −1 for a time klong and a delete bitmap | `toLongs` (`node.getSerializedRef(i)`) | not checked by `parse`. A start checks the records it reads: a key klong's ref must be 0 or more, or −1 if its time is after the startup time (`validateStreamNode`); and in each node's newest version in the section, after Rule R and the cut back to the startup time, no key klong's ref may be −1 or a vpos (`DbStarter.checkStreamPointers`); both SFEs |

### 6.3.1 Klongs

A klong is an `i64`; its type is its two top bits (`Klong`, its class
comment and code):

| Type (bits 62–63) | Name | Bits 0–61 |
|---|---|---|
| 0 | time | the time, in bits 0–55 (`Klong.getTime`: `value & 0x00ffffffffffffffL`); bits 56–61 are 0 (`createTime` asserts the time at most `MAX_TIME`). The class comment's "time value in 58 bits" is not what the code does |
| 1 | key | a compare value (section 7): the segment's bytes in bits 6–61, its length (0 to 7) in bits 3–5, bits 0–2 zero (`Klong.createKey`, `compareValueToKeyKlong`: `compareValue \| TYPE_KEY`) |
| 2 | (none) | deprecated, never written |
| 3 | delete bitmap | bit i (0 to 61) set: klong i of this node is deleted from here on (`Klong.delete`) |

The array is a history, read by `KeyNode.searchEq` and `searchLte`: a
time klong begins the entries of its time (`KeyNode.addKlong` adds one
before the first entry of a later time); a key klong maps its compare
value to its reference, and a later key klong with the same compare value
replaces an earlier one; a delete bitmap removes the klongs whose bits it
sets. A bitmap holds the bits of the node's bitmap before it and its own
(`Dag.appendDeleteKlong` writes `del | arrayDel`, and sets the bit of
every key klong of the deleted compare value), and a reader applies the
latest one it has read (`searchEq`: `deleteBitmap = klong`). A second
delete in the same node by the same transaction changes that
transaction's bitmap in place, when it is the node's last klong. A
reader at time t stops at the first time klong after t. The first klong
of a node is a time klong. In a segment leaf a key klong of
length 0 to 6 names a value node (the key's last segment), never a delete
node: a delete is a delete bitmap in the leaf, and its delete node is
written in its record only, for the rerun at a start (8.14), and named
by no reference (`Dag.setValue`; in the review's check of the scans,
15.2, finding 2, 44,604 such klongs name value nodes, none a delete
node). One of length 7 names the root of the next segment's B-tree; in an inner node, a key
klong names a child, the first with the empty key (`klong 0x4000000000000000`
in the scans). The bound: at most the maximum node size of klongs
(`Dag`'s splits; the scans of `n8` and `n30` have n up to 8 and 30).

## 6.4 The value node and the delete node

A value node holds one key-value pair of a transaction; a delete node,
type 40, the deletion of a key. They are written in their transaction's
record only, once (`StoredValueNode`):

| Off | Size | Type | Field | Meaning and range | Written by | Checked on reading by |
|---|---|---|---|---|---|---|
| 0 | 4 | `i32` | size | `getByteSize`: 8 + 8 + 4 + 4 + L + 4 + 8·k for a value, 8 + 8 + 4 + 4 + 8·k for a delete, rounded up to a multiple of 4 (`Spos.addToAlign(size, 4)`) | `StoredValueNode.toBytes` | not checked |
| 4 | 1 | `u8` | type | 30 value, 40 delete (`node.value == null`) | `toBytes` | `bytesToNode` |
| 5 | 1 | `u8` | format | 4 | `toBytes` | `StoredValueNode.parse`: `VersioningStreamException` |
| 6 | 2 | `u16` | checksum | 6.1, over the node's bytes with the padding zeroed | `toBytes` | `bytesToNode`; `parse` calls the two bytes "not used" |
| 8 | 8 | `i64` | id | 2.5 | `toBytes` (`node.getId()`) | `readNodeHeader` (`ID_OFFSET` = 8), `parse` |
| 16 | 4 | `i32` | offset | the node's offset in its record's bytes (meta blocks not counted): `getSpos(record, offset)` is the node's position | `toBytes` (`bufferOffset`, the offset in the record's buffer) | `parse`: `RecoverableStream.getStartSpos(pos, offset)` throws, an SFE ("Bad offset from transaction"). The node gets its record's position from it (005-34) |
| 20 | 4 | `i32` | L | the value's length, 0 or more (a value node only) | `toBytes` | not checked: `parse` makes `new byte[L]` and copies, so a negative L or one past the buffer throws `NegativeArraySizeException` or `ArrayIndexOutOfBoundsException`, not an SFE (after the checksum has passed) |
| 24 | L | bytes | value | the value (a value node only) | `toBytes` | |
| 24 + L (20 for a delete) | 4 | `i32` | key size | 8·k: the key's segments in bytes, k ≥ 1 | `toBytes` (`key.length * 8`) | `parse`: not a positive multiple of 8 is an SFE ("Bad key size") |
| +4 | 8·k | `i64` | segments | the key, as k compare values (section 7) | `toBytes` (`Bytes.longsToBytesLE`) | not checked |
| | 0–3 | zero | padding | to the size, a multiple of 4; 0 for a delete | `toBytes` (zeroed: "the buffer may hold earlier bytes, and the padding is part of the checksum") | not checked |

So the padding is `(4 − (28 + L) % 4) % 4` bytes for a value, the same as
`(4 − L % 4) % 4`; a delete node is 24 + 8·k bytes. The stored offset is
in record bytes, while the node object in memory keeps the distance in the
stream (`offsetFromTrans`, set by `prepareToSerialize` to
`currentPos − transStartPos`); the two differ when a meta block lies
between the record's start and the node (005-34; the scan of `n8`: the
value node at 200,712, in the record at 199,840, has the offset 744, 128
less than its distance).

## 6.5 References

A reference is what a pointer of a node stores: a top node's root and
skip pointers, a key node's refs. Java writes it by the *record rule*
(`Handle.serializedRef`, item 009, 009-02 section 4.6), called through
`getSerializedRef`:

```java
if (p instanceof ValueNode) return ((ValueNode) p).getSpos();
if (p instanceof Handle) {
    Handle h = (Handle) p;
    Node o = h.obj;
    if (o != null && o.isCanonical()) return o.getSpos();
    long w = h.writtenPos;
    if (Spos.isValid(w) && !Spos.isVpos(w) && (Spos.isVpos(ref) || w > ref)) return w;
}
return ref;
```

That is: a value's position; the position of the node's canonical object
(its latest version, or its vpos if it was never written) if it is in
memory; else the newer of the pointer's reference, raised by Rule R
before the write (`NodeCollection.resolvePointers`, 8.8), and the
position at which this process last wrote the node (`writtenPos`). In
the model's words (docs/sis-model.md, section 4): the latest version of
the child in the stream when the version is written, versions earlier in
the same record included, or the child's id (a vpos) if it was never
written.

Within a record, every node's new position is set before any byte is
written (`prepareToSerialize`), so a node names the new position of a
node written after it in the same record: a top node at the record's
start names the root key node that follows it (the scan of `n8`: the top
node at 1016 has `root=1056`). A reference to a value is always a
position: a value node is written in its own transaction's record, and a
node that points to it is written in that record or later. A reference
can be below the stream's first position, after a cut (section 9.4).


# 7. Keys

A key is a byte string, a *bkey*, of any length from 0. The Core takes
bkeys; the Pub layer's text keys go through an *ikey* first
(`core/doc-files/key-encoding.md`). For the Core's own keys (8.12,
8.13): an ikey is converted to a bkey by `Keys.toBytes(String)`: its
UTF-8 bytes, each `/` (0x2f) as 1 and every other byte plus 2 (as a
signed byte, `b++; b++`; 0xfe and 0xff throw, and an empty ikey is
refused).

**Segments.** A bkey of length `len` is stored as `k = len / 7 + 1`
segments (`Keys.toSegments`: `(key.length + Klong.MAX_SIZE) /
Klong.MAX_SIZE`): segment i holds bytes 7i to 7i + 6, as many as there
are, so every segment but the last has 7 bytes and the last has 0 to 6;
a key of 7·m bytes ends with an empty segment. A segment is a *compare
value* (`Klong.createCompareValue`): byte j of the segment (j = 0 to 6)
at bits 54 − 8j to 61 − 8j, that is `(b & 0xff) << (54 − 8 * j)`, the
length at bits 3–5 (`length << 3`), bits 0–2 and 62–63 zero. A key
klong is its compare value with bit 62 set. Examples (`FormatFacts`,
section 14.6):

| ikey | bkey | segments |
|---|---|---|
| `/a` | `01 63` | `0058c00000000010` |
| `/k/120` | `01 6d 01 33 34 32` | `005b404ccd0c8030` |
| `/1234567` | `01 33 34 35 36 37 38 39` | `004ccd0d4d8dce38`, `0e40000000000008` |
| `/#i/-dummy` | `01 25 6b 01 2f 66 77 6f 6f 7b` | `00495ac04bd99df8`, `1bdbdec000000018` |
| `/#i/dreclaim/-table.txt` | `01 25 6b 01 66 74 67 65 6e 63 6b 6f 01 2f 76 63 64 6e 67 30 76 7a 76` | `00495ac0599d19f8`, `195b98dadbc04bf8`, `1d98d91b99cc1db8`, `1e9d800000000010` |
| `/#i/dreclaim/-current.txt` | `01 25 6b 01 66 74 67 65 6e 63 6b 6f 01 2f 65 77 74 74 67 70 76 30 76 7a 76` | `00495ac0599d19f8`, `195b98dadbc04bf8`, `195ddd1d19dc1db8`, `0c1d9e9d80000020` |

**Order.** Keys are compared segment by segment as unsigned 64-bit
numbers, and a key that is a prefix of the other, in segments, first
(`Keys.compareArrays`, which `Trans.Builder.build`'s `TreeMap` uses;
`Keys.compareKeys` compares signed, the same for compare values, which
are below 2^62). This is the lexicographic order of the bkeys' unsigned
bytes, a prefix first: `FormatFacts` compared the two on 200,000 random
pairs, with zero bytes, 0xff and prefixes, and found no difference.

**In the stream.** A value or delete node stores its key's segments
whole (6.4). The key nodes store one segment each, in key klongs, in the
B-tree of that segment (6.3): the root key node's tree holds the first
segments; a leaf's key klong of length 7 leads to the tree of the next
segment, one of length 0 to 6 to the value (`Dag.putKv`, `Dag.getOne`).

**`Keys.hash`**, used in memory only (the STM's `KeyModSet`), is
`value = 37; value = value * 37 + segment` for each segment, wrapping,
then the absolute value masked to 63 bits. It is in no byte of the stream.


# 8. What decides the bytes

Sections 3 to 7 say what each byte means. This section says what a
writer must do to write the bytes Java writes: which records, with which
nodes in which order, and every number in them. It is the level of the
algorithm, with the code that decides each point; 012-07 to 012-11 port
the code itself.

## 8.1 The inputs

For one sequence of calls, Java's bytes are a function of (P2; the audit,
section 10, checks it):

* **The settings stored in the stream**, which every start reads back:
  the database id, the maximum node size, the startup distance (all in the
  meta blocks, section 3).
* **The settings not stored**, which a writer must be given the same at
  every open: the retain duration (`DbBuilder.retainDuration`,
  `Db.setRetainDuration`; `Long.MAX_VALUE`, forever, by default, with
  which reclaim starts no iteration and makes no cut, but an iteration in
  progress, stored in the table by a run with a finite duration, goes on
  with its steps to its end: 8.13), reclaim's internal fraction (0.25;
  `Db.setReclaimInternalFraction`) and step reserve (4 MiB,
  `Reclaim.DEFAULT_STEP_RESERVE`, or the system property `stepreserve`;
  `DbBuilder.reclaimStepReserve`), and two test settings: the second top
  node's ordinal (`DbBuilder.secondTopOrdinal`, 1) and the record limit
  (`StoredTrans.recordLimit`).
* **The transactions**: their key-value pairs, deletes and read sets, in
  order, and the calls between them that write (`setStartupDistance`,
  8.12) or move the clock (`currentTime`, below).
* **The times.** Every time in the stream is a transaction's, from
  `DbClock.transactionBegin`, which reads the database's clock once:

  ```java
  final long clockTime = clock.getTime();
  long time = clockTime;
  time = time > lastTransactionTime ? time : lastTransactionTime + 1;
  time = time > lastReadTime ? time : lastReadTime + 1;
  ```

  A clock time outside 0 to 2^56 − 1, or a resulting time above it,
  refuses the transaction (`DbException`, 005-18), before it begins.
  `lastTransactionTime` is the last transaction's time (at a start, the
  last record's, `Db.setLastTransTimeOfDbClock`); `lastReadTime` is set by
  `DbClock.currentTime()` (`Db.currentTime()`) to what it returns, the
  clock's time but at least the last transaction's, when no transaction
  runs; it is 0 at a start (finding C3, 10.3). The creation reads the clock
  the same way, with both at 0, so its time is at least 1. `lookupTime`
  never reads the clock.
* **Restarts and crashes**, which change nothing but what 10.3 lists
  (findings C1 to C4) and recovery's fill (4.4).

The cache size, eviction, the buffer's size and time, reads, and when
bytes become durable change no byte of the stream (`EvictionInvariance`,
`StreamDigest`; 10.2).

## 8.2 The creation

A start on an empty stream (length 0) creates the database
(`Db.handleEmptyStream`): the id (`Db.determineDatabaseId`: the builder's,
or `DatabaseId.createRandom()`), then `Db.writePrimordialTransaction`,
which appends 264 bytes (`Db.CREATION_LENGTH`, asserted) in one record:

* the time `tt` from `transactionBegin` (8.1);
* the root key node, `KeyNode.nodeWithTime(tt)`: a segment leaf with one
  time klong, `tt`, whose ref is −1; its id 0, since `x.nextVpos` starts
  at 0 and the creation runs no `ExecuteData.begin`; so its `prevPos` is
  0, its position in memory before the write;
* the first top node, `TopDs.createSuperRootFromFirstKeyNode`: ordinal 0,
  h = 0, root time `tt`, its root pointer the root's handle; its id
  `Spos.nextVpos(0)` = 1;
* the meta block's id, startup distance (the builder's), node size and
  time (`tt`) set; `lastTrans` −1.

The record is written through the normal path (`NodeStream.appendNodes`,
with `startupPos` 0, an empty got-dirty list, and the top node as the
newest written top node), and the meta block at 0 is written before its
first byte (4.2). With the test id, the time 10,000,000,000,000 (T0 of
`MakeStreams`), startup distance 20,000,000 and node size 30 (the stream
`fresh`):

```
pos   bytes                                            field
0     62 65 72 67                                      magic "berg"
4     9a 00 00 00                                      version 154
8     00 a0 72 4e 18 09 00 00                          time tt
16    ff ff ff ff ff ff ff ff                          lastTrans -1
24    7d ee f4 8a 84 66 f3 87 c0 bb 72 9d 2c 8a ab 38  id (testId)
40    00 2d 31 01                                      startup distance
44    1e 00                                            node size 30
46    00 ... 00 (81 bytes)                             reserved
127   0a                                               valid
128   88 00 00 00  05 00 00 00                         record: size 136, format 5
136   00 a0 72 4e 18 09 00 00                          time tt
144   00 00 00 00 00 00 00 00                          startupPos 0
152   a0 00 00 00 00 00 00 00                          topPos 160
160   28 00 00 00  0a 02 80 7e                         top node: size 40, type 10, format 2, sum
168   00 00 00 00 00 00 00 00                          h 0, byte 9, ordinal 0
176   01 00 00 00 00 00 00 00                          id 1
184   00 a0 72 4e 18 09 00 00                          root time tt
192   c8 00 00 00 00 00 00 00                          root 200
200   30 00 00 00  14 02 ca 3c                         key node: size 48, type 20, format 2, sum
208   00 00 00 00 00 00 00 00                          prevPos 0
216   01 01 00 00 00 00 00 00                          leaf 1, n 1, reserved
224   00 00 00 00 00 00 00 00                          id 0
232   00 a0 72 4e 18 09 00 00                          klong 0: time tt
240   ff ff ff ff ff ff ff ff                          ref 0: -1
248   00 00 00 00                                      end of nodes
252   00 00 00 00                                      got-dirty count 0
256   00 00 00 00 00 00 00                             padding (7)
263   0a                                               last byte
```

Between two creations only the time, the id, the startup distance and
the node size can differ; the two checksums depend on the time only. The record
holds the top node before the key node, though `writePrimordialTransaction`
adds the key node to `TransNodes` first: a record holds its top nodes
first (8.3). The start that follows reads the stream back like any other
(`DbStarter.doPrimordialStartup` while the creation is the only record of
the startup section, `DbStarter.isPrimordialTransaction`). Besides the
stream, `FileStream` writes `bergdb.lock` (9.5), and the Pub API's
`created.txt` (`DbBuilder.createdTxt`), which is not the Core's.

## 8.3 A transaction's record

`Db.execute` (`executeInner`), in this order:

1. **Checks before the go point**, which refuse the transaction and
   change nothing that the bytes depend on: `Db.checkSize` (the value
   nodes at most `StoredTrans.valueLimit()`, 7/8 of the record limit); the
   database's state; for a transaction that is not internal, the top node
   ordinals (`LAST_TOP_ORDINAL`) and `Db.checkDirtyNodes` (its index nodes
   at most 15/16 of the record limit, 005-31); `ExecuteData.begin` (8.4);
   `stmCheckConflicts`, the read set against `KeyModSet` (a
   `RerunException`); `transactionBegin`, the time (8.1). Between
   `checkSize` and the lock, `warmup` reads the pairs' keys (no byte).
   A refused transaction writes no record, so these checks decide which
   records exist, and a port computes them exactly as Java: `valueLimit()`
   is `recordLimit / 8 * 7` (integer division first) against the sum of
   the pairs' `StoredValueNode.getByteSizeLong`; `dirtyLimit()` is
   `recordLimit - recordLimit / 16`; `checkDirtyNodes` first passes a
   transaction whose sum of `3 * height * k + 3` over its pairs (k the
   key's segments, `height = 2 + 63 - Long.numberOfLeadingZeros(max(1,
   streamLength / 48))`) is at most `(dirtyLimit - 2 * (40 + 16 * 64 +
   16)) / (32 + 16 * (maxNodeSize + 1) + 16)`, and else refuses it when
   that sum for the pairs with a key transformation plus
   `Dag.dirtyNodeBound` of the other pairs' keys (a sum, 10.2) exceeds
   the same bound. They matter only near the record limit, so in practice
   with a lowered test limit. The STM's refusal is decided the same way,
   by `KeyModSet` (`Keys.hash` of the keys; 4 bins of 32,000 (time, hash)
   pairs, the oldest bin dropped when a fifth is needed; the writes'
   hashes are added after the go point, `stmRecordKeys`): a key read is
   in conflict when a bin holds its hash with a time after the read time,
   and a read time before the oldest bin's first time is refused as too
   old (`KeyModSet.modifiedAfter`); at a start it is empty (C4).
2. **The changes** (`putKvs`): for a reclaim step, first the touch of its
   key range (8.13); then each key-value pair in the transaction's order
   (8.5): `Dag.putKv`, which makes the value or delete node and changes and
   makes index nodes, then the marking of the operation (`endOfOp`, 8.6);
   at the end, `endOfTrans` (8.6).
3. **The record** (`Db.store`): the take (8.7), then the references
   (`resolvePointersOfTakenNodes`, 8.8), the cleaning of the taken nodes
   and the still-dirty test (8.6), the newest written top node (8.10), and
   `NodeStream.appendNodes`, which serializes the record and appends it
   (sections 4.2 and 5).
4. After the record, for a transaction that is not internal, reclaim
   (`Reclaim.transactionCompleted`), which may run its own internal
   transactions, each with its own record, through the same path (8.13).

So a record holds, in order: the top nodes and then the key nodes that
the take chose, each array in the order the take added them (8.7), and
then the transaction's value and delete nodes in the order they were made
(8.5); then the got-dirty list (8.6). A transaction with no key-value
pairs, or whose deletes all name missing keys, still writes a record, with
no value nodes (the scan of `n8`, the record at 520). An internal
transaction (`Trans.isInternal`: the creation, reclaim's table and steps)
skips the ordinal and dirty-node checks and reclaim; the dummy of
`setStartupDistance` is not internal (8.12).

## 8.4 Ids

`ExecuteData.begin` sets `x.nextVpos = nodeStream.getNextPos() + 1`:
the position at which the record will be appended (the stream's length,
or the position after a meta block when the length is inside one), plus
1. Each node that the transaction makes gets the next id
(`Db.setIdOfNode`: the id and the position in memory are `x.nextVpos`,
then `Spos.nextVpos`, +2), in the order in which the Dag reports what it
makes (`Dag.NodeChangeListener`: `topNodeCreated`, `keyNodeCreated`,
`valueNodeCreated`). For a put, `Dag.putKv` makes the next segment's new
leaf (if the key's earlier segments are new) before the value node, and
the value node before the nodes that a split of the leaf makes
(`Dag.setValue`: `valueNodeCreated` before `addKlong` or the split); for a
delete, the split, if any, comes before the delete node
(`appendDeleteKlong` first, then `valueNodeCreated(ValueNode.createDelete(),
key)`). In the scan of `setsd`, the dummy's record at 16,424 gave id
16,425 to the new leaf of the key's second segment and 16,427 to the value
node; in that of `n8`, the record at 568 gave 569 and 571 to its two
values and 573 to 579 to the nodes of the root's split. A port follows the
Dag's order of making nodes exactly. At a start, the rerun gives the same
ids: it counts from `Spos.nextVpos(storedTrans.tpos)` in the same order
(`DbStarter.rerunTransaction`).

## 8.5 The value and delete nodes

`Trans.Builder.build` orders the pairs by key (a `TreeMap` with
`Keys.compareArrays`, section 7) and keeps one per key: a later put
replaces an earlier one, a later delete replaces an earlier delete, and a
delete never replaces a put:

```java
Kv prev = map.put(kv.getKey(), kv);
if (kv.getValue() == null && prev != null && prev.getValue() != null) {
    map.put(kv.getKey(), prev);
}
```

`putKvs` applies the pairs in that order. A put makes one value node,
whatever the value, also an empty one (the scan of `big`). A delete makes
one delete node if the key exists at the transaction's time, and nothing
at all if it does not (`Dag.putKv`: "A delete of a key that does not
exist, a noop. No node must be created"; `appendDeleteKlong` returns
`isNoop`). A pair with a value or key transformation (the Pub API's, and
reclaim's row, 8.13) is transformed when it is applied, and the node holds
the result. Each node is added to the record's `TransNodes` when it is
made, so the value nodes are in the order of the pairs. Its stored key is
the pair's key; its offset is set by the serializer (6.4).

**The key nodes' contents** (added by the review, 15.2, finding 11).
Which klongs a key node holds, and when and how it splits, is decided by
the Dag, and every klong and ref is in the record that writes the node;
this document does not describe it, and a port follows the code exactly:
a klong is appended, with a time klong first if the node has none of the
transaction's time (`KeyNode.addKlong`), while `size + 1 < maxNodeSize`
(`Dag.setValue`, `setNode`) or `size + n + 1 <= maxNodeSize` for n klongs
(`Dag.appendKlongs`); else the node is full (`handleFullNode`): its last
version (`KeyNode.lastVersion`: a time klong, then the live key klongs,
deletes applied, one per compare value, in increasing compare value) is
split in two when it has more than `maxNodeSize / 2` klongs (a space
split, `KeyNode.firstAndSecond`: the first `(size - 1) / 2 + 1`, time
klong included, and the rest), else it replaces the node (a time split,
whose new klongs replace one of the same compare value and time,
`replaceKlong`, or are appended); a node that the transaction made itself
is changed in place instead (`timeSplitInPlace`, `spaceSplitInPlace`); a
replaced node is cut back to before the transaction
(`toPreviousState(tTime - 1)`); a delete sets bits in a delete bitmap
(6.3.1). Each of these steps reports to the
`NodeChangeListener` in its own order, which gives the ids (8.4) and the
marks (8.6).

## 8.6 The got-dirty list

The list of a record is `x.transInfo.gotDirtyNodes` at serialization,
each node as (its id, its position at that moment). It is built in three
steps:

1. **Marking.** During an operation (one pair of `putKvs`, or the
   touch), every index node that it reaches or makes is noted, in order,
   in `opMarks` (`Db.markAtEndOfOp`): the super root when it is read
   (`superRootAccessed`), each node a pointer leads to (`pointerFollowed`),
   each node made (`topNodeCreated`, `keyNodeCreated`) or changed
   (`keyNodeChanged`). At the operation's end (`endOfOp`), if it changed
   something (`opChanged`: a node made or changed, a value or delete node
   made), each noted node that is not yet dirty becomes dirty and is
   appended to the list (`makeDirtyIfNeeded`); the touch's operation
   always marks (`endOfOp(true)`). A node is in the list at most once: a
   dirty node is not appended again.
2. **Replaced nodes** (`endOfTrans`). A node that the transaction replaced
   (`keyNodeReplaced`, `topNodeReplaced`: a full node replaced by a split,
   the super root replaced by a new one) is removed from the list and is
   clean again, unless it is among the first `touchMarks` entries, those
   the touch marked. The others keep their order.
3. **Still dirty** (Rule A, `Db.handleStillDirtyNodes`). After the take,
   the taken nodes are cleaned (`TransNodes.clean`), and then, pass after
   pass until a pass finds none, each taken node, in the record's order (top
   nodes, then key nodes), that is clean and has a pointer to a dirty node
   in memory (`DbHelper.hasDirtyChild`) becomes dirty and is appended
   (`DbHelper.handleStillDirtyNodes`).

The position stored with an id is `node.getSpos()` when the record is
serialized: for a node of step 3, its new position in this record; for a
node of step 1, its last position, or its vpos if it was never written (a
node marked in step 1 was clean, so it was not in D and the take cannot
have taken it). The scans show both: `dirty i=0 id=573 pos=573/0x23d` (a
new node) and `dirty i=0 id=1 pos=160/0xa0` (the first top node, written
at 160).

## 8.7 The take

`TransSeq` is D, the startup section's transactions after the startup
position, oldest first: for each, a `TransInfo` with its position
(`tpos`), its got-dirty nodes (the list of its record, in order) and its
own bytes `o` = `TransSeq.ownBytes(valueBytes)` = 48 + the bytes of its
value and delete nodes (`TransNodes.valueRecordBytes`, the sum of
`StoredValueNode.getByteSizeLong`). `TransSeq` keeps the sums
`dirtyCount` (D, the number of got-dirty nodes) and `ownBytes` (O).

`Db.store` calls, before the record's own `TransInfo` is added to D (so a
record never takes its own transaction's nodes):

```java
final long ownBytes = TransSeq.ownBytes(tn.valueRecordBytes);
long fixedBytes = ownBytes + 16L * x.transInfo.gotDirtyNodes.size();
... (+ the size and 16 of each top and key node already in TransNodes: none)
newSp = transSeq.take(currentSp, nodeStream.getLength(), startupDistance, ownBytes,
        x.transNodes, StoredTrans.recordLimit - fixedBytes);
```

with `currentSp` the startup position before the record (0 at first),
`nodeStream.getLength()` the stream's length, which is the record's
position (4.2), and `startupDistance` the setting in force. `TransSeq.take`:

```java
final long hardSp = streamLength - Math.max(2L * startupDistance, span());
final double share = (double) dirtyCount * recordOwnBytes / ownBytes
        * (streamLength - currentSp) / startupDistance;
final double u = dither(streamLength);
long taken = 0;
long bytes = 0;
while (first != null) {
    final int count = first.gotDirtyNodes.size();
    if (first.tpos > hardSp && taken + count > share && share - taken <= u * count) {
        break;
    }
    if (maxBytes != Long.MAX_VALUE) {
        final long cost = recordBytes(first);
        if (bytes + cost > maxBytes) {
            break;
        }
        bytes += cost;
    }
    newSp = first.tpos;
    for (Node node : first.gotDirtyNodes) {   // top nodes to the top array, key nodes to the key array
        ...
    }
    taken += count;
    dirtyCount -= count;
    ownBytes -= first.ownBytes;
    first = first.next;
    size -= 1;
}
```

and returns `newSp`, the new startup position (`currentSp` if it took
nothing; `take` returns at once when D is empty). What a second
implementation must reproduce exactly:

* `span()` is the newest `tpos` minus the oldest in D, 0 if D is empty.
  `hardSp`, the deadline, is in 64-bit integers; it is negative while the
  stream is shorter than `2 * sd`, and then no transaction is past it.
* `share` is evaluated left to right in IEEE doubles, each `long` or `int`
  converted to double (round to nearest) where it meets a double:
  `((((double) D * (double) o) / (double) O) * (double) (S − sp)) / (double) sd`,
  with `S − sp` subtracted as integers first. O is at least 48 per
  transaction in D, and sd at least 10, so it is finite (but see doubt D9,
  10.4).
* The dither `u` is the finalizer of SplitMix64 on the stream's length, in
  wrapping 64-bit arithmetic with logical shifts:

  ```java
  long z = pos * 0x9E3779B97F4A7C15L;
  z = (z ^ (z >>> 30)) * 0xBF58476D1CE4E5B9L;
  z = (z ^ (z >>> 27)) * 0x94D049BB133111EBL;
  return ((z ^ (z >>> 31)) >>> 11) * 0x1.0p-53;
  ```

  an integer below 2^53 times 2^−53, exact. Values (`FormatFacts`):
  `dither(0)` = 0, `dither(128)` = `0x1.2d05c4045a398p-4`, `dither(264)` =
  `0x1.d7fbc2d9d93d2p-2`, `dither(200000)` = `0x1.b61d270b88e72p-1`,
  `dither(666632)` = `0x1.4000f231c9b68p-1`.
* The test: a transaction is *not* taken, and the take ends, when it begins
  after the deadline (`tpos > hardSp`), it does not fit in what is left of
  the share (`(double) (taken + count) > share`, the sum in integers), and
  the part that fits is not larger than `u` times its count
  (`share − (double) taken <= u * (double) count`). So a transaction with no
  got-dirty nodes is taken while `taken <= share`, or when it is past the
  deadline. `hardSp`, `share` and `u` are computed once, before the loop,
  from D's sums at the call. No double is converted to an integer anywhere
  in the take.
* `maxBytes` is `recordLimit − fixedBytes`, never `Long.MAX_VALUE`, so the
  byte test always runs: `recordBytes(t)` is the sum over its got-dirty
  nodes of the node's size now (`StoredTopNode.getByteSize`,
  `StoredKeyNode.getByteSize`) plus 16. The first transaction that does not
  fit ends the take, also past the deadline; it matters only near the
  record limit.
* The nodes of each taken transaction go, in its list's order, to the
  record's `TransNodes`: top nodes to `addTopNode`, key nodes to
  `addKeyNode`; each array keeps the order of addition, and a node already
  there is not added again (`isInTransNodes`). The record holds all the top
  nodes first, then all the key nodes (`Serializer.prepareToSerialize`,
  `serializeNodes`).

`Db.store` then sets the record's `startupPos` to `newSp` and, after the
append, adds the record's own `TransInfo` to D (`tpos`, `lastPos`, `tt`,
`startupPos`, `ownBytes`, and its got-dirty list, steps 1 to 3 of 8.6),
and sets the startup position to `newSp`.

**Checked.** A script (`check_scan.py`, 14.6) replays the take from the
scans alone, as described here: D from the records after the startup
position, each with its got-dirty count and own bytes (48 + the sizes of
its value and delete nodes), `S` the record's position, sd from the meta
blocks, and the dither. It gives every record's `startupPos` in all the
streams of `MakeStreams`, 3,780 transactions taken because they fit,
1,515 by the dither, 45 by the deadline alone, and 9 stops at
transactions that twice the setting alone would have taken (the span
term), with restarts, reclaim's records and three `setStartupDistance`s
among them (the stream `deadline` was made for the last two cases).

## 8.8 The references of the taken nodes

Before the taken nodes are cleaned, `Db.resolvePointersOfTakenNodes`
calls `NodeCollection.resolvePointers` on each, in the record's order:
each pointer to an index node, unless it holds a canonical object or is a
stream pointer below the stream's first position (left as it is; doubt D2,
10.4), is resolved: if the node of its id is pinned (its canonical object
is in the node table and dirty: in D or in this record), the pointer gets
that node's live handle, so the reference written is the canonical
object's position, its new one if it is in this record; else its
reference is raised to the node's newest version in the startup section
if that is newer (Rule R, `Spos.newer`). Then the record rule (6.5)
gives each reference written. A port reproduces the record rule's result:
for every pointer, the latest version of the node at the moment the record
is serialized, or its vpos if it was never written. It computes it as Java
does, from what the pointer holds (Rule R's map of the last start's
section, the canonical object, `writtenPos`), not from a table of every
node's latest position, which would grow with the database; that the two
agree is the model's claim, checked by Java's audit (INV-SLOT) only for
the nodes its oracle knows, and otherwise by the byte tests (doubt D1;
the review, 15.2, finding 19).

## 8.9 The startup position

The record's `startupPos` is `newSp` from the take (8.7): the position of
the last transaction it took, or the startup position before the record if
it took none. It never decreases. 0 means the first record (the creation
writes 0, and records keep 0 until the first take takes something). A
start reads from the last committed record's `startupPos` (4.3), and the
transactions after it are D again (8.14).

## 8.10 topPos

`Db.store` chooses the newest written top node: the one written last
before (`newestWrittenTop`), or the record's top node with the largest
ordinal if it has a larger one (`t.topNodeId > top.topNodeId`). The
serializer writes its position after `prepareToSerialize`, so its new
position if it is in the record; and after the append it is the newest
written top node. The creation's record names its own top node (160). The
start takes it from the last record's `topPos` (`DbStarter`), which must
be the super root at the startup time (an SFE else).

## 8.11 The meta blocks and the padding

The meta blocks inside or right after a record are written as the record
is appended (4.2), from the in-memory block: `lastTrans` is the record
before. The padding is `computeZeroCount` (section 5). Nothing else in a
record depends on where it falls relative to the meta blocks but the
value nodes' stored offsets (record bytes, 6.4) and the positions.

## 8.12 setStartupDistance and its dummy transaction

`Db.setStartupDistance(n)`:

1. `n < 0` throws `IllegalArgumentException`. `n` is clamped to 400,000
   (`2 * META_BLOCK_DISTANCE`) to 1,000,000,000.
2. Under the write lock, the database's state is checked as a
   transaction's is (005-53: a refused call changes nothing). If `n` is the
   setting in force, nothing is written (005-53, `fd8f513`).
3. The setting and the in-memory meta block's startup distance are set to
   `n`, and the transaction `put("/#i/-dummy", 200,000 zero bytes)`
   (`DbConstants.DUMMY_KEY`, two segments, section 7) is executed as a user
   transaction: not internal, so the dirty-node check and reclaim run for
   it. If it is refused or fails, both are set back and the exception is
   thrown.

Its record holds a value node of 200,044 bytes (24 + 200,000 + 4 + 16,
no padding), so it crosses at least one meta block, which carries the new
setting (the scan of `setsd`: the record at 16,424 crosses 200,000, and
that block has `startupDistance=500000`); its take already uses the new
setting. The key is an ordinary key: it is in the database, and later
calls put it again.

## 8.13 Reclaim's records and its table

Reclaim (`Reclaim`) writes internal transactions, after a user
transaction's record and under the same lock
(`Reclaim.transactionCompleted`, called with the user transaction `t`,
whatever the retain duration; it returns at once for an internal one).
A retain duration of forever (`Long.MAX_VALUE`, the default) stops only
the new iterations (step 1) and the cuts (step 4, where
`t.tt - retainDuration > tEnd` never holds): an iteration in progress,
the table's last row not done, as a run with a finite duration stored
it, goes on with its steps (step 2) after a restart with the default or
`setRetainDuration(Long.MAX_VALUE)`, and the table is stored at its end
and when it gets safe (step 3); the review's probe showed it (15.2,
finding 1). With `streamSize = t.nextPos` (the position after `t`'s
record):

1. **A new iteration** when none is in progress (the last row of the
   table is done, or there is none), the retain duration is not
   `Long.MAX_VALUE` (tested first, so that the product below is not
   computed then), and
   `streamSize > lastPStart() + 2L * db.getStartupDistance()` and
   `t.tt - lastTStart() >= (long) (ITERATION_SPACING * retainDuration)`
   (`ITERATION_SPACING` = 0.25; `lastPStart()` 0 and `lastTStart()`
   `Long.MIN_VALUE / 2` with no row). The new row has `pStart = streamSize`,
   `tStart = t.tt`, `pCut` = `streamSize` for the first row, else the last
   row's `pStart`; it is appended, and the table is stored (below).
2. **A step**, when an iteration is in progress and
   `allowed = (long) (internalFraction * (streamSize - current.pStart)) - current.rewritten`
   is above `MIN_STEP_SIZE` = 10,000: `step(current, min(allowed, 16,000))`
   (`MAX_STEP_SIZE`). One internal transaction (`Reclaim.step`):
   * a scan of the key-value pairs at time `tStart`, after `lastKey`
     (exclusive), through the maintenance follower; it counts
     `key.length * 8 + value.length + 100` per pair and stops after the pair
     that takes the count above the size, or when the index nodes it has
     followed exceed `max(1, stepReserve / (80 + 48 * maxNodeSize))`, or at
     the end (`eod`). `eod` is set only when the scan runs out of pairs
     (`Dag.getMany` calls `eod()` only then), not when the count stops it
     at the last pair: the next step then scans nothing, touches to the
     end, and ends the iteration;
   * for each pair scanned, its value now (the first read at the latest time
     fixes the step's lookup time; the others read at it): if it exists and
     its record is before `pCut` (`gd.tpos != Spos.NULL && gd.tpos < it.pCut`),
     `keyRead(key)` and `put(key, value)`, and `rewritten +=
     key.length * 8 + value.length + 28`;
   * the row's put: `/#i/dreclaim/-current.txt` with a value transformation
     that, when the pair is applied, adds the transaction's `dirtiedBytes`
     so far to the row's `rewritten` and stores the row's text (below). The
     pairs are applied in key order (8.5), so `dirtiedBytes` counts the
     touch and the puts of the keys before the row's key;
   * the transaction's read time is the step's lookup time; it is a touch
     (`t.touch`) of the keys after `lastKey` up to the step's last key (to
     the end at `eod`): `Db.touchRange` makes every index node on the way
     dirty before the puts (8.6), and `dirtiedBytes` adds up the sizes of
     the nodes it and the puts make dirty (`makeDirtyIfNeeded`);
   * the new row has the step's last key as `lastKey` and
     `kvCount` increased by the pairs scanned;
   * a `RerunException` drops the step (it is tried again later); after the
     step the row is the new one, and at `eod` the row becomes done, with
     `tEnd = t.tt` and `pEnd = t.tpos` of the step's transaction, and the
     table is stored.
3. **Safe positions** (`markSafePositions`): each done row with `pSafe`
   −1 whose `pEnd` the startup position has passed gets
   `pSafe = streamSize`; if any did, the table is stored.
4. **A cut** (`pretruncateIfPossible(t.tt)`): the done row with the
   largest `pStart` such that `t.tt - retainDuration > tEnd`, `pSafe` set
   and passed by the startup position, `pCut` at or before the record that
   the last valid meta block names (`getLastTransPosOfLastValidMetaBlock`),
   and `pCut` after the first available position. If there is one and it is
   not cut yet: the rows with a smaller `pStart` are removed, the row is
   marked cut, the table is stored, the first available position and time
   become its `pCut` and `tEnd`, and the cut is pending. The files are cut
   later (`cutIfDurable`, 9.4); that writes no byte.

**The table** is stored by `Reclaim.storeTable`: an internal transaction
`put("/#i/dreclaim/-table.txt", text)`, where the text is the UTF-8 of
each row's text followed by `----next----\n`, the rows in table order.
**A row's text** (`IterationInfo.serialize`, through `StringMap`) is 11
lines `name=value\n`, in the order of `StringMap`'s `HashMap`, which for
these 11 names is fixed (finding in 10.2):

```
pCut=5041560
tEnd=0
cut=false
pStart=5574880
tStart=10000289400000
lastKey=26177508076421160
rewritten=102488
pEnd=-1
pSafe=-1
done=false
kvCount=466
```

The numbers are `"" + long` (`Long.toString`: decimal, a minus sign when
negative); `cut` and `done` are `true` or `false`; `lastKey` is the key's
segments as signed decimals separated by one space, or `null` before the
first step. `pEnd` and `pSafe` are −1 until set; `tEnd` 0. The row of the
iteration in progress, under `/#i/dreclaim/-current.txt`, is one row's text
without the separator.

At a start, `Reclaim.initFromDb` reads both keys back (at
`Long.MAX_VALUE`): the table's rows, and the current row, which replaces
the table's row with the same `pStart` when neither is done (so the
iteration in progress resumes after its last step); the first available
position and time are the `pCut` and `tEnd` of the cut row with the
largest `pStart`, or 0 and 0. It makes a cut that the table marks but the
files do not show yet, and writes nothing. The retain duration, the
internal fraction and the step reserve are not stored (8.1); a cut that
was pending (decided, not yet made) is made here, so nothing else of it
needs to be kept.

## 8.14 What a start rebuilds

A start rebuilds what decides the next records, so that a restart between
two transactions leaves the bytes as they are (P2;
`RestartInvariance`), but for findings C3 and C4 (10.3):

* the in-memory meta block: the last valid block, `lastTrans` the last
  committed record (4.3); the startup distance from it;
* the startup position: the last record's `startupPos`;
* D (`DbStarter.rerunTransactions`): a `TransInfo` for each record after
  the one at the startup position, with its `tpos`, `lastPos`, `tt`,
  `startupPos`, own bytes (48 + its value and delete nodes'
  `getByteSizeLong`), and its got-dirty nodes from its stored list, in its
  order, each made dirty; the record at the startup position itself is
  not in D;
* the nodes those transactions made, rerun with the same ids (8.4), at the
  positions of their newest versions in the section (`newById`), so that
  `prevPos` and the references are what they were;
* the newest written top node, from the last record's `topPos`;
* the clock's last transaction time, the last record's time;
* reclaim's table and current row (`initFromDb`).

Not rebuilt: `DbClock`'s `lastReadTime` (C3), the STM's `KeyModSet` (C4),
and `FileStream`'s file size, which comes from the files (C1, 9.3).

A start appends nothing to the stream but the creation on an empty one
(8.2) and recovery's fill after a crash (4.4); a physical cut that the
table marks (`initFromDb`) deletes files and appends nothing. A close
appends nothing at all: it writes and forces what the buffer
holds. Reads, syncs and the settings that are not stored append nothing
either; `setStartupDistance` appends its dummy (8.12).


# 9. The directory

## 9.1 The files

A database in a directory (`FileStream`) is its stream in files named
`NNNNNNNNNNNNNN.bergdb`: the 14 digits are the file's first position
divided by 100,000 (`BYTES_PER_INDEX_UNIT`), zero-padded
(`FileStream.indexToString`). The files hold the stream from the first
position to its end, each file the bytes from its first position on,
without gaps. The stream's first position is that of the first file; its
length, the last file's first position plus its length. Other files in
the directory are not the stream's: `bergdb.lock` (9.5), and the Pub
API's `created.txt`.

## 9.2 The sizes and how a file is chosen

A new file is made when an append has bytes left after filling the last
file to its capacity (`FileStream.append`), so at a stream length that
is the full file's end, a multiple of 100,000 (`FileStream.newFile`; a
`Bug` otherwise). How the bytes reach `FileStream` (the buffer's chunks)
does not matter. A new file gets a capacity from `FILE_SIZES`: 200,000, 1,000,000, 5,000,000, 20,000,000,
100,000,000, 500,000,000, 2·10^9, 10^10, 5·10^10, 2·10^11 bytes. A file is
filled to its capacity before the next is made. The capacity is chosen by
`applyFileSizeChangeRules` when the file is made, from the current index
`c`, the stream's length `L` and its size `S = L − firstPos`:

* `found`: the largest index `i ≥ 1` with `FILE_SIZES[i] <= S / 4`, or 0
  if there is none;
* if `found` is larger than `c`: the index becomes `found` only when `c`
  is not the largest (with `setMax2G`, a test setting, the index of 2·10^9)
  and `L % FILE_SIZES[c + 1] == 0`; else it stays `c`;
* if `found` is smaller than `c`: it becomes `found` at once;
* with `max2G`, when the current index `c` (not the result) is above that
  of 2·10^9, the result is that index; since the rule tests `c`, a jump
  up from below can still pass it once (`setMax2G` has no caller outside
  `FileStream`'s tests).

An empty directory gets `00000000000000.bergdb` with index 0. Opening an
existing directory (`determineFileSizeIndexFromFiles`) sets the index to
the smallest `i` with `FILE_SIZES[i] >=` the larger of the last two files'
lengths (the last one's alone if it is the only one), and the last file
takes appends up to that capacity (`openForRw`). In the scans every file
before 4 MB is 200,000 bytes (`n8`: four files, the last 66,632).

## 9.3 What a restart and the cut change

The bytes of the stream do not depend on the files, but the names and
sizes of the files can differ between two runs with the same bytes:

* **C1**: a restart can change the layout from there on, since the open
  rule above takes the capacity from the lengths of the last two files: a
  1,000,000-byte file begun at 4,000,000 and opened again when it holds
  104,880 bytes, after a file of 200,000, takes 200,000 bytes only (the
  audit's `FileLayoutProbe`: 200,000-byte files from 4.0 MB with the
  restart, one of 1,000,000 without).
* **C2**: the size of each new file depends on `getFirstPos()`, which
  moves when reclaim's physical cut is made (9.4), and that moment depends
  on durability, which is timing.

So two directories of one workload are compared by their bytes, as the
concatenation of their files from the decided cut (`StreamDigest` does
so); with the same restarts and without reclaim, the files are the same
too (10.3).

## 9.4 The cut

Reclaim decides a cut at `pCut` (8.13), a record's position. The files
are cut when the stream is durable up to the length at the decision
(`Reclaim.cutIfDurable`: `db.getDurableLength() >= pendingCutDurableAt`),
by `FileStream.pretruncate(pCut)`: every file that ends before `pCut`
(`spos + fileLength − 1 < pos`) is taken off the stream at once, and the
first position becomes the first remaining file's first position, at or
before `pCut`; a thread of its own deletes the files later, oldest first,
forcing the directory after each (005-46). So the first position is a file
boundary, a multiple of 100,000, and the bytes between it and `pCut`
remain. `getFirstAvailablePos()` is the decided cut, `pCut`. A start whose
table marks a cut that the files do not show makes it (`initFromDb`).
Reads below the first position throw `ReadBelowFirstPosException`.

## 9.5 What Java refuses, and the lock

`FileStream`'s constructor (`handleExistingFiles`, `checkDbFiles`)
reads the `.bergdb` files sorted by name (`String.compareTo`) and throws
`BadDirStateException` (an `IOException`) when:

* a name, without `.bergdb`, is not a number: `stringToIndex` strips
  leading zeros and parses the rest as a `long`; it must be from 0 to
  `Long.MAX_VALUE / 100,000`. Java writes 14 digits, but accepts any such
  number ("Bad name of bergdb file"), and `Long.parseLong` takes a
  leading `+` and any Unicode decimal digits: `+6.bergdb`, `0000+6.bergdb`
  and `٦.bergdb` are file 6 (found by 012-06; checked with
  `Long.parseLong`);
* a file's first position is not where the files before it end ("are not
  in a correct state");
* a file other than the last has a length that is not a multiple of
  100,000 ("Bad size of file").

`checkDbFiles` checks the files one by one in name order, each its name,
then its first position (not for the first file), then its size (not
for the last), so the first failing check in that order gives the
message: a bad size of a file is refused before a gap after it.

The stream format's own checks (sections 3 to 6) come at the start. The
directory is created if missing. `bergdb.lock` is created if missing, with
a fixed text of 225 bytes in UTF-8 (`FileStream.LOCK_TEXT`: "This
directory contains a BergDB database. BergDB locks this file\n" and three
more lines), never changed or deleted; the lock is an exclusive lock on
one byte at 2^62, held while the stream is open (005-63). A directory
locked by another stream is refused with `DirectoryInUseException`.


# 10. The determinism audit

Step 4 of the plan (14.3): every use in the Core of what could make the
bytes differ between two runs of one workload with the same clock and
settings, and why it does or does not. Made by a subagent at max effort
for this task (2026-10-28, 13:58 to 14:30), checked here where it matters
(the table order, the probes of C3 and C4, the startup maps); its probes
and runs are in `/Users/f/fl/bench/012/02-out/audit/` (outside the
repository).

## 10.1 Scope and method

The 143 production files of `common`, `core`, `dag`, `storage`, `stream`
and `pub/util`, without the tests (`*Tester.java`, `DbTester*`,
`nanotest`, `@Nano` methods, and the test parts of production classes:
`Reclaim.Tester`, `Eviction.Twin`, `NodeCollection.TestStream`,
`Cache3.bin`, `DbStarter.PrevMap`). Searched: hash collections and every
way they are iterated, randomness, clocks, identity hashes, thread ids,
system properties, `Runtime`, doubles and casts, threads, waits,
`volatile` and atomics, sorts, charsets, `String.format`. Not in the
Core: `Hashtable`, `ConcurrentHashMap`, `WeakHashMap`,
`ThreadLocalRandom`, `UUID`, `Instant`, `identityHashCode`. No `Node`
class overrides `hashCode` or `equals`, so a `HashSet<Node>` is an
identity set. Left out as never in the writer, startup or reclaim, or out
of 012's scope: `Jmx`, `DbUtil`, `DbScan`, `DagComparison`,
`KvComparison`, `ReadOnlyStream`, `DagNodeIterator`, `Salsa`,
`SalsaStream`, `KeyFactory`, replication (`DbHelper.AddReplicaClass`,
`StorageManager`'s replica rules), `SeedGenerator` (only the random id),
`BuildInfo` and `Util.today` (only `created.txt`), `StatsNodeVisitor`,
`CacheStats`, `HashUtil`, `DummyStream`, `OneFileStream`, `Create.set`,
`MyLongSet`, `EventToWaitFor`, `Bytes`' float helpers (Pub API only),
`MemoryStream` and `CutStream` (they store the bytes as given).

Each use is (a) unable to reach the bytes, (b) reaching them
deterministically, or (c) a real dependence, a Java bug by P2.

## 10.2 The result

**The bytes by position have no class-(c) dependence** on hash order,
randomness, floating point, eviction, the write buffer, threads or
readers. The writer, startup and reclaim decide from transaction times,
positions, settings, and state that a start rebuilds from the stream. The
database id is random by default, a setting that can be fixed. Java's own
checks agree: `EvictionInvariance` (every eviction schedule, with
restarts and reclaim) and `StreamDigest`'s three modes gave identical
streams at `404d2ee`, and two JVM runs of `MakeStreams` give the same
bytes in all its directories (14.6). Four class-(c) findings concern
restarts and the files (10.3).

The uses, by class (file:line at the reference; (b\*) is an input by
design):

| Use | Class | Why |
|---|---|---|
| `TransSeq.take` (`:159-196`): `hardSp`, `share`, the test, `maxBytes`, the order of nodes | b | integers, doubles in Java's order, list order (8.7); no double becomes a long |
| `TransSeq.dither` (`:233-238`) | b | wrapping 64-bit products, logical shifts; exact |
| `TransSeq.checksum` (CRC32) | a | tests only |
| `Db.opMarks` (`ArrayList`), `endOfOp` | b | the order of the operation's marks (8.6) |
| `Db.replacedInTrans` (identity set) | a | membership only; `endOfTrans` keeps the list's order |
| `Db.checkDirtyNodes`, `Dag.dirtyNodeBound` (`IdentityHashMap` `walked`, `HashMap`s `freshKeys`, `below`) | b | a sum of integers over distinct nodes, deeper first; it only refuses before the go point |
| `Db` access data (`-cache.accessClock()`) | a | never written as a reference: every pointer made by the Dag has a node (doubt: latent if one had none) |
| `Db` statistics (`Aux.dirtyFraction*`), `writersWaiting`, the closer thread, `evictPos` | a | getters, eviction's yielding, close |
| `DbClock.currentTime`, `transactionBegin` (`:105`, `:123`) | b | the only reads of the clock; `lastReadTime` (C3) |
| `SystemClock` | b\* | the default clock; its times are inputs. Its "strictly increasing" branch never runs: `lastTime` stays 0 |
| `CoreTestClock`, `TestClock` | b | a plain field (doubt D8) |
| `DbStarter` `posMap`, `newById`, `posToId` (`HashMap`s), iterated in `updateStreamPointers`, `createMemoryPointers`, `registerSectionNodes` | b | filled in stream order; each iteration changes only its entry's own node, reading maps it does not change, and `posMap` holds one version per id; so the order does not matter (checked here in the code) |
| `DbStarter.linkD`'s `byPos` (from `Cache3.handles()`) | a | contents only; D is visited in `TransSeq` order |
| D and the got-dirty lists at a start | b | rebuilt in record order from the stored lists (8.14) |
| `NodeCollection.idByPos` (`LinkedHashMap`, a cache), `MaintenanceFollower.read` | a | lookups; the result is the same without them |
| `NodeCollection.indexIds` (`HashSet`) | b | only its size is used, a count |
| `NodeCollection.resolvePointers` skips pointers below `getFirstPos()` | b | doubt D2 |
| `Reclaim`: `(long) (ITERATION_SPACING * retainDuration)` | b | `0.25 * (double) r`, truncated; not `r / 4` above 2^53 (2^55 + 5 gives 9007199254740994, `r / 4` 9007199254740993) |
| `Reclaim`: `(long) (internalFraction * (streamSize - current.pStart))` | b | in range; a NaN fraction passes `setInternalFraction`'s check and gives 0: no step |
| `Reclaim`: `maxNodes`, the scan's estimate, `rewritten`, `dirtiedBytes` | b | integers and key order (8.13) |
| `Reclaim.cutIfDurable` (`getDurableLength`) | a for the bytes, c for the files | C2 |
| `Reclaim` statistics (`Stats`, `TouchCounter`'s `IdentityHashMap`) | a | only after `enableStats()` |
| `StringMap` (`HashMap`, `serialize` iterates `entrySet`) | b | the 11 names of a row come out in one order, `pCut, tEnd, cut, pStart, tStart, lastKey, rewritten, pEnd, pSafe, done, kvCount`: `String.hashCode`, capacity 16, no resize, buckets 1, 2, 3, 4, 7, 8, 8, 8, 12, 13, 14, bucket 8 in insertion order (`lastKey, rewritten, pEnd`). A fact of the JDK's `HashMap` since Java 8, not of the language; checked by `FormatFacts` |
| `TransNodes` arrays | b | insertion order, unique by node flags; the periodic reset of its arrays (`clear`) is (a) |
| `DbHelper.handleStillDirtyNodes` | b | passes in `TransNodes` order; a dirty child is resident (pinned) |
| `Trans.Builder.build` (`TreeMap`, `Keys.compareArrays`) | b | key order, the duplicate rule (8.5) |
| `StoredTrans.recordLimit` (static volatile) | b | a test setting |
| `StoredTrans.Serializer`'s buffers (sizes, every 97th shrink) | a | every byte of a record is written explicitly, the padding from `ZEROS64` |
| `NodeStream`, `RecoverableStream`: meta blocks by position | b | 4.2 |
| Eviction (`Eviction`, `Cache3`, `Residents`, `Handle`): system properties `evict`, `evictseed`, `evictbudget`; `Random(seed)`; `nanoTime`; the evictor thread; the CLOCK step; `table.handles()` order | a | eviction runs under the write lock between transactions, never at a start; it takes only written, unpinned objects, not the newest written top node; the record rule (6.5) writes a pointer as the node's latest position whether its object is resident, evicted or loaded again (`Cache3.kill` sets `writtenPos`); a reloaded node is its latest version; the step reserve counts ids |
| `BufferedStream`, `StorageManager`: the consumer thread, the buffer time, `computeRules` | a for the bytes | one writer appends in order; only when and in what pieces the bytes go out varies; the durable length reaches only the cut (C2) |
| `FileStream`: names from positions | b | 9.1 |
| `FileStream`: sizes (`applyFileSizeChangeRules`, the open rule) | c for the files | C1, C2 |
| `FileStream.pretruncate`, its thread, `LOCKED_DIRS` | a for the bytes | which front files exist when varies (012-01, 3.2, point 8) |
| `DatabaseId` (`SecureRandom` seeded by `SeedGenerator`: `nanoTime`, `currentTimeMillis`, memory, threads' stacks, properties, `Math.random`) | b\* | random unless `DbBuilder.id` or `testId()`; from the stream at a start |
| `KeyModSet` (4 bins of 32,000 pairs, in memory) | b, c across a restart | refusals before the go point; `Keys.hash` wraps; C4 |
| `Jmx` getters call `db.currentTime()` | a, left out | they move `lastReadTime` (doubt D4) |
| `Audit` (`Integer.getInteger("audit")`) | a | checks only |
| Text: `StringUtil.toBytes`, `Keys.toBytes` | b | explicit UTF-8; numbers by `Long.toString`, not locale-dependent |
| `volatile` publication for readers (`KeyNode.size`, `TopNode.spos`, `Handle.obj` and others) | a | the writer runs alone under the write lock |

## 10.3 Findings: real dependences

Four class-(c) findings, each shown by a probe (the audit's,
`/Users/f/fl/bench/012/02-out/audit/`; C3 and C4 run again here,
`02-out/verify/`, with the same results). C1 and C2 concern the files:
the concatenated bytes were identical. C3 and C4 concern the bytes: a
restart between two transactions changes the next record, against P2
(010-01), which quotes Frans's goal of 2015-12-28: "a restart can be
inserted between any two transactions without affecting the bytes in the
stream". By 012-01, 9.2 they are Java bugs to register in
005; C follows Java until they are fixed.

* **C1. A restart changes the file layout.** `FileStream` reopens the
  last file with the capacity implied by the larger of the last two files'
  lengths (`determineFileSizeIndexFromFiles`, `:715-735`; `:701`). Probe
  `FileLayoutProbe` (10,000-byte puts, test clock and id, node size 30, sd
  1 MB, to 5.8 MB): without a restart, `00000000000040.bergdb` of
  1,000,000 bytes and `…050` of 805,704; with a restart after the
  transaction at stream 4,104,880, `…040` to `…048` of 200,000 each, then
  `…050` of 805,704. The concatenation is the same
  (SHA-256 `fea5269b...`). A port of the open rule, with the same restart
  points, gives Java's layout.
* **C2. When the physical cut is made changes the later files.** The cut
  is made at the first user transaction at which the durable length has
  reached the length at the decision (`Reclaim.cutIfDurable`); the durable
  length grows by the buffer's thread (20 ms) and by syncs; `FileStream`
  sizes each new file from `length − firstPos` (`:926`). Probe
  `CutLayoutProbe` (1,500 transactions 10 ms apart, 10,000-byte values on
  50 keys, sd 200,000, retain 1 s), four modes: the decided cut 15,861,104,
  the stream 18,207,728 bytes and the SHA-256 of the bytes from the
  decided cut identical in all four; the first position at the end and
  the files holding those bytes differ (synced after every transaction:
  15,800,000, files of 200,000 from `…158`; no sync: no cut made, files of
  1,000,000 from `…150`; with pauses: 10,000,000, and earlier files of
  200,000). A C clone without threads cuts at its own points: its
  directory after a cut cannot match Java's, file for file (question Q1).
* **C3. `DbClock.lastReadTime` is not restored at a start.** Probe
  `RestartStateProbe clock`: put `/a`; the clock set to T2;
  `currentTime()` (returns T2); [restart]; put `/b` with the clock still
  at T2. Without the restart `/b` gets T2 + 1 (10000000100001), with it
  T2 (10000000100000); both streams 472 bytes, different SHA-256. With the
  system clock a restart takes longer than a unit, so it does not happen
  in practice; with a test clock it does.
* **C4. `KeyModSet` is empty after a start.** Probe
  `RestartStateProbe stm`: put `/k` at T1; put `/k` at T2; [restart]; at
  T3 a transaction with `lookupTime(T1)`, `keyRead("/k")`, and a put of
  `/j`. Without the restart it is refused (`RerunException`; stream 472
  bytes); with it, it commits (stream 560 bytes). An empty bin has
  `firstTime` −1 (`KeyModSet.java:125`), so neither a conflict nor "too
  old" is found. This is also a gap in the STM's serializability: the
  transaction read `/k` at T1, `/k` changed at T2, and it still commits.

## 10.4 Open doubts

Not proved, and not shown false by any probe:

* **D1.** The record rule under eviction and readers' swizzles (6.5):
  traced, and backed by `EvictionInvariance` and `StreamDigest`'s reads
  mode; not proved for every path.
* **D2.** `resolvePointers` and `linkToCanonical` skip pointers below the
  physical first position, which depends on when the cut was made (C2).
  Argued to give the same reference either way (such pointers name
  replaced nodes, neither pinned nor newer in the section); the four runs
  of `CutLayoutProbe` and `StreamDigest` agree from the decided cut. It
  matters more for C than for two Java runs: a C clone without threads
  makes its physical cuts at its own points (C2), so its first position
  differs from Java's after every cut, and its bytes equal Java's only if
  D2 holds; 012-05's cross sets with reclaim test it, from the decided
  cut (the review, 15.2, finding 13).
* **D3.** `dirtyNodeBound` counts objects; it equals a count of nodes if
  there is one object per node during the call, which holds under the
  write lock.
* **D4.** Any caller of `currentTime()` (`Jmx.DbMonitor`, another thread)
  moves `lastReadTime`; with a clock that does not advance, the next
  transaction's time moves by one unit.
* **D5.** Under a steady fast load the physical cut was not made in the
  runs without syncs (likely each decision moves the durable target on);
  operational, not a matter of the bytes.
* **D6.** The setters of the retain duration, internal fraction, step
  reserve, cache size and startup distance can be called from other
  threads; they take effect at the next transaction or step, a race only
  in multi-threaded workloads.
* **D7.** Asserts and `AssertStatus.enabled()` paths are checks; a grep
  found no side effect in them, not exhaustive.
* **D8.** The test clocks' time is a plain field: a clock set on one
  thread and read by a transaction on another has no happens-before.
* **D9.** The stored startup distance is not validated at a start
  (`MetaBlock.checkFormat` checks the magic, `lastTrans` and the time):
  0 or less would make the take's `share` infinite or NaN; C must then
  follow IEEE, without traps.

## 10.5 What a second implementation must reproduce

From the class-(b) uses: the take's arithmetic exactly (8.7; IEEE binary64
with round to nearest, no contraction, `-ffp-contract=off`, `FLT_EVAL_METHOD`
0, wrapping 64-bit integers, logical shifts); Java's conversion from
double to long where reclaim makes one (NaN to 0, saturation; 012-01,
6.2); reclaim's integers and doubles (8.13); the table's text with its
fixed name order; `DbClock` with `lastReadTime` (in memory, 0 at a start,
not changed by `currentTime` while a transaction runs); the orders of 8.5
to 8.7; `dirtyNodeBound` as a sum (any order within a depth); the record
rule (6.5, 8.8); `KeyModSet` (in memory, empty at a start); the settings
of 8.1; `FileStream`'s naming and size rules with the open rule (C1).
Not needed: eviction's choices, the buffer's timing, the access clock,
statistics, `Jmx`, `Audit`, readers' swizzles.


# 11. Differences from the text of 2015

`core/doc-files/stream-format.txt` (July 2015) and the comments in the
format classes, against the code at the reference. The code wins.

1. **The meta block's last byte.** `MetaBlock`'s class comment says
   "META_BLOCK_LAST_BYTE. 1 is used to indicate that the block is valid";
   the code writes and checks 10 (`META_BLOCK_LAST_BYTE =
   (byte) Util.identity(10)`). The 2015 text does not give it.
2. **The meta version's field.** The 2015 text: bytes 4–5, "Range [133,
   2^16-1]"; `MetaBlock`'s comment: 4 bytes, "as an int". Both hold: the
   code writes an `i32` and reads bytes 4–5 as a `u16`
   (`FILL_OUT_TEMPLATE` writes a `u16`), and accepts 154 only.
3. **The startup distance.** `MetaBlock`'s comment: "Typically 20M". The
   default has been 50,000,000 since 2026-10-13 (`DbBuilder`).
4. **`lastTrans`.** "spos of last valid transaction completely written
   before the meta block": a block written by recovery's fill names the
   record of the last valid block before it instead, possibly −1 (4.4).
5. **The record format.** The 2015 text has "Trans format version. One
   byte, range: [2, 127]" and format 2; the format is 5 since 2026-10-15
   (`topPos` in the header), written as an `i32` whose upper bytes are
   zero. The header is 32 bytes: size, format, time, `startupPos`,
   `topPos` (not in the text).
6. **The record size.** The 2015 text: "Range: [5, 2^31-1]"; the walker
   refuses below 17, the smallest record Java writes is 48, and the writer
   refuses above `MAX_RECORD_SIZE` = 2^31 − 9 (005-17).
   `RecoverableStream`'s comment gives 2^31 − 1, the reader's bound.
7. **The node header.** The 2015 text gives size, type and version
   (bytes 0–5) only; bytes 6–7 are the Fletcher-16 checksum (named in its
   2015.4 release notes). Its size range "[6, 2^31-1]": `NodeStream.readNode`
   refuses 6 and less.
8. **The versions.** The 2015 table ends at 2015.4: Meta 154, Trans 2,
   Top 2, Key 2, Value 2. At the reference: 154, 5, 2, 2, 4.
9. **The maximum node size** at meta bytes 44–45 (005-50) is not in the
   2015 text; its reserved bytes start at 46 now.
10. **Klongs.** `Klong`'s comment: a time klong's "time value in 58 bits
    (bits 0:0-7:1). 4 bits are unused"; the code uses bits 0–55
    (`MAX_TIME` = 2^56 − 1, `getTime`), and bits 56–61 are zero.
11. **The value node's bytes 6–7.** `StoredValueNode.parse` skips them as
    "two bytes not used"; they are the checksum, checked before the parse.
12. **The value node's offset.** The field is the offset in the record's
    bytes (005-34), while the node object in memory keeps the distance in
    the stream (`offsetFromTrans`): the comment of `toBytes` says so; older
    texts do not.
13. **Words.** The 2015 text and `RecoverableStream` call records
    "transactions"; this document says records, and keeps "transaction"
    for what a record stores.
14. **A key klong's first byte** (added by the review, 15.2, finding 18).
    `Klong`'s comment: "First byte is stored in bits 6:3-7:2", bits 51 to
    58; the code (`Klong.createKey`, `createCompareValue`) puts byte j at
    bits 54 − 8j to 61 − 8j, the first at 6:6-7:5 (section 7). The
    comment's "DATA, 56 bits at 0:6-7:5" is right.
15. **Smaller comments** (the review, finding 18). `StoredKeyNode.toLongs`:
    "6 zero bytes available" after the leaf flag and the size; there are
    5, bytes 19 to 23 (its parser says 5). `Spos`: value nodes "can start
    at any mod8 value"; since 2015-11-14 a value node's size is a multiple
    of 4 (`StoredValueNode`), so it starts at a multiple of 4 (2.4).
    `RecoverableStream.MIN_TRANS_SIZE`: "a 16-byte header and the last
    byte"; the header is 32 bytes since format 5, and 17 stays the walk's
    bound (4.3).


# 12. The scanner's format

`StreamScan` (`c/test/cross/java/StreamScan.java`) is Java's scanner: it
prints one line per item of a stream, from the raw bytes, and runs
Java's parsers and record walk alongside as a check, printing an `error`
line where they refuse a record or disagree with the raw fields. C's
scanner (012-06) prints the same text, so two scans compare with `diff`.
The format, "streamscan 1", is defined in the class's header, which is
its reference; this section maps its fields to the document.

Usage: `test/cross/java-build.sh`, then
`java -ea -cp build/java/classes bergdb.core.StreamScan PATH` (from
`items/012-bergdb-c/c/`), where `PATH` is a database directory or a flat
file holding a stream from position 0. Exit status 0 if no `error` line.

| Line | Fields | Section |
|---|---|---|
| `streamscan 1` | the format's name and version | |
| `file name= first= size=` | a `.bergdb` file, in name order; `first` its first position from its name | 9.1 |
| `other name= size=` | any other file of the directory | 9.1, 9.5 |
| `stream first= length=` | the first readable position and the length | 2.2 |
| `meta pos= magic= version= time= lastTrans= id= startupDistance= maxNodeSize= reserved= last=` | a complete meta block; `version` is the `i32` at 4–7; `reserved` is `zero` or the hex of bytes 46–126 | 3 |
| `meta pos= partial= bytes=` | the first bytes of a block cut by the end | 4.4 |
| `gap from= to=` | bytes not scanned, in a cut stream, before the record where the walk starts | 9.4 |
| `record pos= size= format= b5= time= startupPos= topPos= last=10 lastPos= next=` | a committed record's header; `b5` the hex of bytes 5–7 | 5 |
| `record pos= size= last= sha256= next=` | a record that is not committed, not parsed | 4.1, 4.4 |
| `torn pos= size= have=` | a record cut by the end (`size=?` if fewer than 4 bytes) | 4.4 |
| `top ... h= b9= ordinal= id= rootTime= root=`, then `  skip i= pos= time=` | `h` read as a signed byte | 6.2 |
| `key ... prevPos= leaf= n= reserved= id=`, then `  klong i= raw= ... ref=` | `n` a signed `i16`; `reserved` bytes 19–23 | 6.3 |
| `value ... id= offset= length= sha256= keySize= segs= key= ikey= pad= padZero=` | `offset` the stored offset; `key` the bkey; `ikey` only when printable | 6.4, 7 |
| `delete ... id= offset= keySize= segs= key= ikey= pad= padZero=` | the same without the value | 6.4 |
| `nodes-end pos= off=`, `gotdirty pos= off= count=`, `  dirty i= id= pos=`, `padding pos= off= count= zero=`, `last pos= byte=` | the record's end | 5 |
| `end length=` | the end of the scan | |
| `error ...` | a failed check; its text is the implementation's own | |

The common node fields are `pos= off= size= type= format= sum= sumOk=`
(6.1): `sum` the stored checksum in 4 hex digits (`u16`, byte 7 then byte
6), `sumOk` whether it equals Fletcher-16 with bytes 6–7 as 0. Numbers are
decimal; a pointer is printed `decimal/0xhex`, except −1, printed `-1`; the hex is `Long.toHexString`'s, lower case without leading zeros (`296/0x128`), and a negative pointer other than −1, which only a corrupt stream has, is printed as its signed decimal and the 16 hex digits of its two's complement (`-2/0xfffffffffffffffe`; `StreamScan.ptr`).
Items come in the order of their first byte; a meta block inside a record
comes after the item it falls in or after.

Points where the text is precise beyond the header's words:

* A time klong prints `time=` as bits 0–61 in decimal (`k &
  0x3fffffffffffffff`); Java's `getTime` reads bits 0–55, the same for
  every klong Java writes (bits 56–61 zero, 6.3.1).
* A key klong prints `key len=` (bits 3–5) and `bytes=`, the `len`
  bytes from bit 54 down; bits 0–2 appear only in `raw`.
* `ikey=` is printed when every byte of the bkey, mapped back (1 to `/`,
  every other byte minus 2, modulo 256), is printable ASCII 0x21 to 0x7e
  and not `=`; for an empty key that is true, and the line has `key=
  ikey=` with nothing after either.
* `segs=` lists the segments in 16 hex digits, comma-separated; `key=`
  is the bkey rebuilt from them, each segment's bytes by its length.
* The walk starts as Java's does
  (`RecoverableStream.getPosOfTransCompletedBefore` of the first
  position): at the record named by the first valid meta block at or after
  the first position that names one at or after it, −1 meaning 128. A
  directory's files must be named by 14 digits, be contiguous, and all but
  the last have lengths that are multiples of 100,000; the scanner stops
  with an exception otherwise (Java accepts any number as a name, 9.5).

Changes to the format or the scanner since step 2 are logged in 14.6.


# 13. Questions for Frans

**Q1. Comparing directories after reclaim's cuts (finding C2).** 012-01's
done-when item 3 asks for "the same files, with the same names and bytes"
also with reclaim, from the decided cut. C2 shows that Java itself gives
different files there from one run to another: the names and sizes of the
files after a physical cut depend on when the cut was made, which is
timing. Options:

* (a) For workloads with reclaim, compare the concatenated bytes from the
  decided cut (`getFirstAvailablePos()`), not the files; as
  `StreamDigest` does. Without reclaim, compare the files, with the same
  restart points (C1).
* (b) Make Java's file layout a function of the stream (for example, new
  files sized from the decided cut, not the physical one), a 005 entry
  and a Java change, and then compare files everywhere.
* (c) Leave item 3 as it is: not reachable.

Recommendation: (a) now, which is what 012-01, 3.2 point 8 meant, and C2
registered in 005 so that (b) can be decided there. 012-05's `cross.sh`
compares the file names and bytes from the file that holds the cut on
(`compare_dirs`); its full set passed, Java against Java, since below a
live stream of 4 MB every new file has 200,000 bytes whatever the first
position (9.2), or since the two runs' timing agreed. With C, whose cut is
not timed as Java's, a workload with reclaim and a live stream above 4 MB
would differ in its file names after the cut, so (a) also means a change
of `compare_dirs` for such workloads before 012-11.

**Q2. Restarts that change the bytes (C3, C4).** Two pieces of state that
decide the bytes are not rebuilt by a start: `DbClock.lastReadTime` (a
transaction's time can differ by one unit after `currentTime()` and a
restart with a clock that has not moved) and the STM's `KeyModSet` (a
transaction whose read time is before a restart is refused without the
restart and committed with it, a serializability gap). Options:

* (a) Register both in 005; C ports Java as it is. Comparisons of Java
  with C at the same restart points are not affected, as both forget the
  same state; comparisons of a run with restarts against one without
  (`RestartInvariance`, `StreamDigest`'s restarts mode against its plain
  mode) must avoid the two cases (no `currentTime()` right before a
  restart with a clock that does not move; no read time before a
  restart) until Java is fixed.
* (b) The same, and fix Java first (C4 at least, as it is a correctness
  gap), before 012-09 and 012-10 port the clock and the STM.

Recommendation: (a) for 012's pace, with C4 marked in 005 as a correctness
bug for a fix soon; C follows the fix when it comes (012-01, 9.2).


# 14. How it was made

This section is the task's plan, as approved, and its progress.

## 14.1 The goal

A complete definition of BergDB's stream and directory, as Java writes
them at the reference commit: every byte, so that a second implementation
can read and write them. Today the code is the only definition (012-01,
3.1); `core/doc-files/stream-format.txt` of 2015 is partial and out of date
in places.

Done when:

1. Every field of the meta block, the framing, the record and the three
   nodes is described: its offset, size, type, meaning, range, and the
   Java method that writes it and the one that checks it on reading.
2. The directory is described: file names, sizes, how a file is chosen,
   what a cut removes, what Java refuses (`BadDirStateException`).
3. What decides the bytes is described, at the level a writer needs:
   which index nodes a record holds and in what order (the take), the
   startup position, `topPos`, ids and vpos, the got-dirty list, the
   padding, the creation's 264 bytes, the dummy transaction, reclaim's
   table. Each points to the Java code that decides it.
4. The determinism audit (14.3, step 4) is done and written.
5. `StreamScan`, Java's scanner, prints every field of a stream, and every
   field it prints is in the document. It runs on every stream of 012-05's
   sets without an unexplained line.
6. The differences from `stream-format.txt` are listed (one is known: the
   meta block's last byte is 10, not the 1 of `MetaBlock`'s comment).

## 14.2 Read first

* Java: `MetaBlock` (126 code lines), `RecoverableStream` (421),
  `StoredTrans` (521), `StoredKeyNode` (112), `StoredTopNode` (142),
  `StoredValueNode` (142), `NodeChecksum` (46), `NodeStream` (241),
  `Klong` (191), `Keys` (197), `Spos` (26), `FileStream` (661, the naming,
  the sizes and the cut), `TransSeq` (186, the take), `Db`'s creation
  (`writePrimordialTransaction`), `setStartupDistance`, and
  `Reclaim.IterationInfo` with `StringMap`.
* `core/doc-files/stream-format.txt` and `key-encoding.md`.
* `docs/sis-model.md` (records, D, the startup position) and 011-11, the
  Level 2 alignment, for the meaning of the record's fields.
* 012-01, section 3.

## 14.3 The work

1. **Pin the reference.** Record `main`'s HEAD; the document describes
   that commit and says so at its top.
2. **`StreamScan.java`**, first, as 012-05 needs it: a program in package
   `bergdb.core` (to reach the parsers) that reads a directory or a flat
   file and prints one line per item: each meta block with its fields; each
   record's header; each node with all its fields (klongs and pointers in
   decimal and hex, values as length and SHA-256, keys as hex); the
   got-dirty list; the padding (and whether it is zero); the last byte. A
   fixed text format, documented in the file's header, which C's scanner
   (012-06) prints too. It lives in the C directory's
   `test/cross/java/` (012-01, decision D1) and is compiled against the
   Core Layer as 012-01, 6.3 says.
3. **Write sections 1 to 9**, reading each field's writer and
   reader, and checking each claim with `StreamScan` on streams made for
   the purpose (a few `CoreSame`-like workloads: node sizes 8 and 30, a
   small startup distance, reclaim, a setStartupDistance, a crash).
4. **The determinism audit.** Every use in the Core of hash-ordered
   collections (`HashMap`, `HashSet`, `IdentityHashMap` and their
   iteration), `Random`, clocks (`currentTimeMillis`, `nanoTime`, and
   every read of the database's clock, which 012-01, 4.4 found at two
   points of `DbClock`), `identityHashCode`, floating point, and thread
   timing, as far as the writer, the startup and reclaim reach: for each,
   whether it can change the bytes, and why not. 012-01, 3.2 found the
   first ones harmless (`DbStarter`'s maps, `Dag.dirtyNodeBound`); this
   completes the list. A real dependence is a Java bug (P2): registered in
   005, and C follows Java's behaviour until it is fixed.
5. **Review** at max effort by a second agent that did not write it: the
   document against the code, field by field.

The document's sections, as planned: 1, the reference and the versions;
2, numbers, positions and alignment; 3, the meta block; 4, the framing
and recovery; 5, the record; 6, the nodes; 7, keys; 8, what decides the
bytes; 9, the directory; then the determinism audit, the differences from
2015's text, and the scanner's format.

## 14.4 Tests

`StreamScan` on every stream of 012-05's sets; and two runs of one
workload in two JVMs give the same scan (P2, as a check of the audit).

## 14.5 Notes

* Describe what Java does, also where it looks odd; propose nothing. A
  question for Frans goes at the end, with options.
* Where the document lives: decision D6b of 012-01, so it moves to
  `docs/stream-format.md` when 012-10 is done.

## 14.6 Progress

* 2026-10-28 13:47: started by a subagent of 012's conductor, in the
  scratch clone `/Users/f/fl/bench/012/02-stream-format/` (a clone of
  `bergdb` at `404d2ee`). Reference recorded at the top. Next: step 2,
  `StreamScan`.
* 13:55: step 2 done. `c/test/cross/java/StreamScan.java` (text format
  "streamscan 1", in its header) and `MakeStreams.java` (test streams:
  fresh, n8, n30, restarts, big, setsd, reclaim, crash cuts and their
  recoveries; `java ... bergdb.core.MakeStreams build/streams`). Every
  stream scans without an error line; Java's parser and record walk agree
  with the raw fields; a flat copy scans as its directory; two JVM runs of
  `MakeStreams` give the same bytes in every directory. Marker
  `/Users/f/fl/bench/012/02-scanner-ready` written. Scans in
  `c/build/scans/` (ignored). Next: steps 3 and 4, the document.
* 13:56: stopped at the conductor's request (012's effort raised; a new
  agent at max effort continues from this clone). Sections 1 to 9, the
  audit and the lists are not written yet. Read so far: `MetaBlock`,
  `RecoverableStream`, `StoredTrans`, the three `Stored*Node`,
  `NodeChecksum`, `NodeStream`, `Spos`, `Klong`, `Keys`, `FileStream`'s
  naming and checks, `TransSeq` (take, dither), `TransNodes`, `Db`'s
  creation, `execute`/`store`, marking (`endOfOp`, `endOfTrans`),
  `DbHelper.handleStillDirtyNodes`. Not yet: `DbStarter` in full,
  `Reclaim`/`StringMap`, `DbConstants`, `DbClock`, `FileStream`'s size
  choice and cut, `Trans.build` (kv order), the audit's grep.
* What the scans and the code show, for the document (each still to be
  checked once more against the code when written):
  * The creation (264 bytes, `Db.writePrimordialTransaction`): root key
    node id 0 (even: `x.nextVpos` starts at 0, not reset by `begin()`),
    super root id 1; record at 128, startupPos 0, topPos 160; top node
    h=0 ordinal 0; key node leaf=1, n=1, one time klong with ref -1,
    prevPos 0 (its spos before the write was its id 0); 7 zero bytes of
    padding. The meta block's time is the creation's time and stays so in
    every later meta block seen (setTime only at creation?).
  * Ids: `setIdOfNode` gives a new node the vpos `x.nextVpos`, which
    `ExecuteData.begin()` sets to the next record's position + 1 and each
    node advances by 2 (`Spos.nextVpos`), in creation order; a value
    node's id is so its record's pos + 1, + 3, ... (seen: 265, 385).
  * Got-dirty list: (id, spos) at serialization time; a node not yet
    written has spos = its vpos (odd, = id), one written in this very
    record has its new position (prepareToSerialize sets spos first).
    The list and the record header carry no checksum: a byte changed in
    the list passes Java's parser (probe: flip byte 500 of n8's flat copy).
  * A key node written the first time has prevPos = its vpos (odd).
  * Version: written as an int at 4 to 7, read as an unsigned short at 4
    (`readMetaBlock`, `getVersion`); `FILL_OUT_TEMPLATE` writes a short.
  * Record format byte: written as the int 5 at bytes 4 to 7
    (`serializeHeader`), read as one byte with three skipped.
  * Value node: bytes 6-7 are its checksum, though `parse` calls them
    unused; padding to a multiple of 4, zeroed (`toBytes`); its stored
    offset is in record bytes (`getStartSpos` inverts it, 005-34).
  * Top node: the root pointer is ref 0; skip pointer i is set exactly
    when bit i of the ordinal is; an unset one is written (-1, -1).
  * Recovery's fill writes a valid meta block copied from the last valid
    one (so lastTrans may be -1 at 200,000: recovered-199993).
  * `setStartupDistance` clamps to at least 400,000; the builder allows
    from 10.
  * A cut stream (reclaim): the scan, as Java's walk, starts at the
    record named by the first valid meta block at or after the first
    position; the bytes before it are a `gap`.
  * Two JVM runs of MakeStreams give the same bytes in all 25 directories
    (P2 check for the audit; `diff -rq -x bergdb.lock`).
  * Determinism audit, found so far: `DbStarter` uses HashMaps (posMap,
    newById, posToId, byPos, PrevMap) and `Db.replacedInTrans` an identity
    set (membership only); their iteration is still to be checked.
* Next: write sections 1 to 9 field by field from the code read above,
  each checked with a scan (`c/build/scans/*.txt`, remade by
  `MakeStreams` then `StreamScan`); then the audit (grep the Core Layer
  for HashMap, HashSet, IdentityHashMap, Random, currentTimeMillis,
  nanoTime, identityHashCode, double/float, threads); then the
  differences from `stream-format.txt` and the scanner's format. Done
  item 5's "every stream of 012-05's sets" stays open for the conductor.
* 14:31 to 14:40 (a second agent, at max effort, from the same clone):
  read the plan, `StreamScan`, `MakeStreams` and the progress above. The
  determinism audit (step 4) was given to a subagent at max effort, which
  reported at 14:30 (section 10; its probes in
  `/Users/f/fl/bench/012/02-out/audit/`). Read: `MetaBlock`,
  `RecoverableStream`, `NodeStream`, `StoredTrans`, the three
  `Stored*Node`, `NodeChecksum`, `Spos`, `Klong`, `Keys`, `TransSeq`,
  `TransNodes`, `Db` (creation, start, `execute`, `store`, marking,
  `setStartupDistance`), `DbHelper.handleStillDirtyNodes`, `DbClock`,
  `Trans.build`, `Reclaim` (iterations, steps, table, cut), `StringMap`,
  `FileStream` (names, sizes, open, cut, lock), `DbStarter` (maps, rerun,
  top node), `TopDs.newSuperRoot`, `Handle.serializedRef`.
* 14:47: sections 1 to 7 written (`FormatFacts`, a probe outside the
  repository, `/Users/f/fl/bench/012/02-out/probes/`, printed the key
  segments, the table text, the key order check and dither values).
  Next: sections 8 to 13.
* 14:52: sections 8 (what decides the bytes) and 9 (the directory)
  written. The audit's probes for C3 and C4 run again
  (`/Users/f/fl/bench/012/02-out/verify/`): the same results. Next:
  sections 10 to 13, the scanner's start of walk (14.6's first finding),
  then a last pass over the document against the code.
* 14:56: sections 10 (the audit, from the subagent's report, checked
  where it matters), 11 (the differences) and 12 (the scanner's format)
  written, and 13 with two questions for Frans (Q1 on C2, Q2 on C3 and
  C4).
* 14:57: **`StreamScan` changed** (not its text format): where the walk
  starts, a valid meta block whose `lastTrans` is −1 now means the record
  at 128 only if 128 is at or after the first position, as in Java's
  `getPosOfTransCompletedBefore`; before, the scanner tried to read at 128
  in a cut stream and stopped with an `IOException`. Such a block can come
  from recovery's fill (4.4) in a stream later cut. A synthetic stream
  (the second file of `recovered-199993` alone, first position 200,000)
  now gives the same refusal as Java's walk, as `error` lines. The 25
  streams of `MakeStreams` scan exactly as before (`cmp`, all exit 0).
  Next: a check of 8.6, 8.7, 8.9, 8.10, `prevPos` and `lastTrans` against
  the scans by a script, then a last pass over the document.
* 15:00: `MakeStreams` has a new stream, `deadline` (an empty
  transaction; a 1.5 MB value at sd 600,000, so that the take's deadline
  decides; sd raised to 2,000,000 and 5,000,000 with 2.4 and 12 MB of
  values and lowered to 400,000 each time, so that the deadline's span
  term decides), 1,807 records, 17 MB; two JVM runs give the same bytes.
  `check_scan.py` (`/Users/f/fl/bench/012/02-out/probes/`, outside the
  repository; `python3 -I check_scan.py c/build/scans2/*.txt`) replays the
  take from the scans and checks the got-dirty positions (8.6), the ids of
  value and delete nodes (8.4), `prevPos` (6.3), `topPos` (8.10) and the
  meta blocks' `lastTrans` (3): 0 errors on all 26 streams, every
  record's `startupPos` replayed (numbers in 8.7). Scans of this run in
  `c/build/scans2/` (ignored).
* 15:02: a pass of my own over the document against the code, from the top:
  sections 1 to 8.6 re-read, small fixes (when each version is checked,
  wordings in 3, 4.2, 4.4, 5, a reference in 6.3, the creation's
  checksums). **Paused at the conductor's request** (the 5-hour usage
  window at 86 percent, resets at 15:50); all committed. **Next step**:
  go on with that pass from 8.7 to the end (8.7 to 13), then the status
  line at the top (the document written, the review of step 5 still to
  come) and the report to the conductor. Done-when item 5 stays open
  for 012-05's sets.
* 15:54: resumed at the conductor's message. `main` merged into the
  clone (`2f3514f`: 012-04 and 012-05; `java/` unchanged since `fd8f513`;
  StreamScan and MakeStreams in `main` are those of `ff1627f`, unchanged
  since; the clone's untracked `java-build.sh` moved to
  `/Users/f/fl/bench/012/02-out/java-build.sh.clone-untracked`, `main`'s,
  which also compiles StreamDigest, taken). `cross.sh quick KEEP=1`: OK,
  and all 105 scans of its views, crash cuts and planted copy have only
  lines of section 12's kinds, and one `error` line, in the planted
  copy's scan, the planted byte (it is a value node's length: "bad key
  size", and `sumOk=false`), which is what that copy is for. `cross.sh
  full KEEP=1` started in the background for the same check.
* 15:57: my pass over the document finished (8.7 to 13): the take's rule
  for a transaction without got-dirty nodes made exact, what a start and a
  close append (8.14), and Q1 completed with what `cross.sh` compares
  (file names from the cut file on, which C2 can change above 4 MB).
* 16:08: `cross.sh full KEEP=1` in the clone: CROSS full OK, 278
  workloads, 1,262 crash cuts, 6 in turns, 0 differences (688 s, at
  `nice`). Its 2,375 scans (1,112 of the views, both sides by both
  scanners; 1,262 of the crash cuts; the planted copy) have only lines of
  section 12's kinds, and one `error` line, in the planted copy's scan, as
  in the quick set. `check_scan.py` on side A's 278 scans: 0 errors,
  299,401 takes replayed of 300,852 records (206,383 transactions taken
  because they fit, 37,832 by the dither, 1,601 by the deadline alone; the
  span term decides only in `MakeStreams`' `deadline`), and the got-dirty
  positions, value ids, `prevPos`, `topPos` and `lastTrans` as 8.6, 8.4,
  6.3, 8.10 and 3 say. Outputs kept in `c/build/cross/` (ignored); the
  checks' outputs in `/Users/f/fl/bench/012/02-out/`.
* 16:16: **Done when** (14.1): 1 (every field: sections 3, 5, 6), 2 (the
  directory: 9), 3 (what decides the bytes: 8), 4 (the audit: 10), 6 (the
  differences: 11) hold; 5 holds for 012-05's quick and full sets (every
  field `StreamScan` prints is in 12; no unexplained line); the scale set
  is not run (by hand, 10M keys). Findings for 005 (the conductor
  registers them): C1 to C4 (10.3). Questions for Frans: Q1, Q2 (13).
  StreamScan unchanged since `ff1627f` (in `main`). **Next**: the review,
  step 5, by a second agent at max effort (started by the conductor), on
  this file at the clone's HEAD.


# 15. The review

Step 5 of the plan (14.3): an independent review of this document
against the Java code, field by field, at max effort. By Claude (Opus 5.5,
Claude Code), the reviewing agent, a subagent of 012's conductor, which
did not write the document. Started 2026-10-28 16:22, in the scratch clone
`/Users/f/fl/bench/012/02-review/` at `1955718` (`java/` as at `fd8f513`,
so as at the document's reference, `404d2ee`). Probes of the review are in
`/Users/f/fl/bench/012/02-review-out/` (outside the repository).

## 15.1 What was checked, and how

* **The code, field by field**, at the clone's HEAD: `MetaBlock`,
  `RecoverableStream` (append, read, recovery, the iterators,
  `getSpos`, `getStartSpos`, `isIncompleteCreation`), `NodeStream`,
  `StoredTrans` (header, serializer, parser, limits), the three
  `Stored*Node`, `NodeChecksum`, `Spos`, `Klong`, `Keys`, `TopNode`,
  `TopDs`, `KeyNode` (adds, splits, `lastVersion`, validation), `Dag`
  (puts, deletes, splits), `Handle.serializedRef`, `NodeCollection`
  (`resolvePointers`, the maintenance follower), `TransSeq`, `TransNodes`,
  `DbHelper`, `Db` (constructor, start, creation, `execute`, the checks,
  `store`, marking, `putKvs`, `touchRange`, `setStartupDistance`),
  `DbClock`, `DbStarter`, `Trans`, `KeyModSet`, `Reclaim` (all of
  `transactionCompleted`, `step`, the table, the cut, `initFromDb`),
  `StringMap`, `DbBuilder`, `DatabaseId`, `DbConstants`, `SystemClock`,
  `FileStream` (names, sizes, open, cut, lock) and `StreamScan`; the
  2015 text against section 11.
* **The bytes**: the 26 streams of `MakeStreams`, made again in
  `/Users/f/fl/bench/012/02-review-out/streams/` (3 s) and scanned with
  `StreamScan` (all exit 0); the creation's 264 bytes by `xxd` against
  8.2's dump (equal); the key segments of section 7 recomputed
  (`keys_check.py`, equal); the order of the row's names of 8.13 from
  `String.hashCode` and `HashMap`'s buckets (`hashorder.py`, equal); a
  stored table read from the stream (`valueat.py`: 11 lines a row in
  that order, `----next----` after each).
* **An independent replay** (`replay.py`, written without the author's
  `check_scan.py`) of the take with its doubles, dither and deadline
  (8.7), the record's index nodes and their order (top nodes first, each
  in the order the take met them, once), `prevPos` (6.3), the got-dirty
  positions (8.6), the value ids (8.4: odd, after the record, increasing),
  `topPos` (8.10) and the meta blocks' `lastTrans` (3), from the scans
  alone: 0 differences on `MakeStreams`' streams (5,928 records, 27,558
  index nodes) and on 012-05's quick set (`cross.sh quick KEEP=1`, CROSS
  quick OK, 20 s; 6,192 records, 37,258 index nodes) and on the full
  set's 278 scans that the author kept (`02-stream-format`'s
  `c/build/cross/full/a/*/scan-by-a.txt`, read only: 299,401 records,
  1,979,848 index nodes in the record's order, 1,851,704 `prevPos`,
  2,030,278 got-dirty positions, 801,057 value ids, 299,401 `topPos`,
  4,898 `lastTrans`), but for one artefact of the script (a torn record
  of `cut-200131`, which it does not count as the block's writer). Two
  more runs of `MakeStreams`, the author's at 15:00 and this one, give
  the same bytes in all 26 directories (`diff -rq`, `bergdb.lock` left
  out). `scancheck.py`, on `MakeStreams`' streams, the quick set and the
  full set (1,880,135 key nodes): every key node's first klong is a time
  klong, time klongs and bitmaps have the ref −1, no time klong has bits
  56 to 61, no key klong bits 0 to 2.
* **Reclaim's table** (`reclaimcheck.py`, from the scans and the
  directories' bytes) on `MakeStreams`' `reclaim`, the probe's stream and
  the quick set's three workloads with reclaim: 38 stored tables, each row
  11 lines in 8.13's order, and each table explained by 8.13's steps: 10
  new iterations (`pStart` the table record's position, `tStart` the user
  record's time, `pCut` the row before's `pStart`, the initial fields),
  10 ends (`pEnd` and `tEnd` the step's record), 10 safe positions (`pSafe`
  the position after the last user record), 6 cuts; 177 steps' rows; the
  first table of two cut streams not classified (no table before it in
  the scan).
* **Probes** (`probes/src/bergdb/core/ReviewProbe.java`, run with the
  probe classes first on the class path): `retain-forever` (finding 1),
  `short` (finding 21).
  `files_check.py`: 9.2's rule gives the names and sizes of the files of
  six `MakeStreams` directories without restarts (`deadline`: 37 files,
  20 of 200,000, 16 of 1,000,000 from 4 MB, and from 20 MB one of a
  capacity of 5,000,000, holding 2,719,920), all equal.

## 15.2 Findings

Severity: **error**, a C port from the document would be wrong;
**omission**, a writer (or reader) would lack something it needs;
**minor**, wording or a reference. Fixed in the document unless said.

1. **Error, fixed (8.1, 8.13).** "`Long.MAX_VALUE`, forever, by default,
   which turns reclaim off" and "Reclaim (with a retain duration other
   than forever) writes internal transactions". `Reclaim.transactionCompleted`
   (`Reclaim.java:322-353`) tests the retain duration only for a new
   iteration (`:331`) and, through `t.tt - tRetain > row.tEnd`, for a cut
   (`:670`); a step needs only an iteration in progress (`:342-348`), and
   `markSafePositions` none (`:576-590`). So a database whose table has a
   row not done goes on with its steps, and stores the table at the row's
   end and when it gets safe, after a restart with the default retain
   duration or after `setRetainDuration(Long.MAX_VALUE)`. Probe
   `ReviewProbe retain-forever`: retain 2 s until a row is in progress
   (80 transactions, stream 72,272), restart with forever, 400 more
   transactions: the iteration completed, and the scan shows a step's
   record (`-current.txt`, at 96,656) and two of the table (104,440 and
   112,584) after the restart. A C port that skips reclaim when the
   duration is forever writes other bytes.
2. **Error, fixed (6.3.1).** "In a segment leaf a key klong of length 0
   to 6 names a value or delete node". It names a value node only: a
   delete is a delete bitmap (`Dag.appendDeleteKlong`), and the delete
   node is made only for the listener, so it is written in its record
   (for the rerun) and named by no klong (`Dag.setValue`,
   `Dag.java:678-685`). Checked with `scancheck.py` on the 26 streams of
   `MakeStreams` (44,604 such klongs name value nodes, none a delete node;
   5,865 name positions not in the scans, in the cut stream `reclaim`)
   and on the full set's 278 scans (3,577,250 name value nodes, none a
   delete node; 491,630 positions outside the scans, in gaps and cut
   streams).
3. **Minor, fixed (2.5).** "The one exception is the creation's root key
   node, whose id is 0": the creation's top node, id 1, is the other
   exception to "the odd numbers from its record's position + 1 up" (it
   would be 129).
4. **Omission for a reader, fixed (6.3, the columns "Checked on reading
   by" of n, klong and ref).** A start validates every node of the records
   it reads (`DbStarter.validateTransactions`, `validateNode`,
   `KeyNode.validateStreamNode`, `KeyNode.java:1619-1662`): a key node with
   n = 0 is an SFE, and a key klong's ref must be 0 or more (−1 is let
   through after the startup time); and `DbStarter.checkStreamPointers`
   (`:682-723`) refuses −1 or a vpos in the newest versions after Rule R
   and the cut back. The table said "not checked". Not bytes, but 012-06
   and 012-14 refuse what Java refuses. `validateStreamNode`'s
   `checkIncreasingTime` (`KeyNode.java:1569-1583`) never updates its
   `time`, so it checks nothing; its `checkLastTimeIndex` cannot fail on
   parsed bytes either: a slip in Java for the conductor, not changed.
5. **Minor, fixed (6.2, ordinal).** "above `MAX_TOP_NODE_ID_VALUE` an
   SFE": the test (`StoredTopNode.java:106`) cannot fail, as `>>> 16` of
   a long leaves 48 bits.
6. **Minor, fixed (5, `startupPos`).** "`Db.getStartupPosFromLastTransaction`
   asserts `>= 0` and walks from it": it asserts it for each record it
   walks from the meta block's record; the walk from the startup position
   is `Db.readTransactions` (4.3).
7. **Minor, fixed (2.3).** `getStartSpos` throws for `pos < 0` too
   (`RecoverableStream.java:349`).
8. **Minor, fixed (5, size).** "to `recordLimit` = 2^31 − 9": the size is
   a multiple of 8, so at most 2^31 − 16; `prepareToSerialize` compares
   the aligned size with the limit (`StoredTrans.java:649-655`).
9. **Omission, fixed (8.3, step 1).** The refusals before the go point
   decide which records exist, but their arithmetic was given as "7/8"
   and "15/16" of the limit: `valueLimit()` is `recordLimit / 8 * 7`
   (`StoredTrans.java:70-72`), not `recordLimit * 7 / 8`, and
   `checkDirtyNodes` (`Db.java:2059-2100`) has a cheap bound from the
   stream's length before `Dag.dirtyNodeBound`. Added, with `warmup`,
   and the rule of `KeyModSet`, which decides the STM's refusals the same
   way (`KeyModSet.java:51-96`).
10. **Minor, fixed (9.2).** "with `max2G`, an index above that of 2·10^9
    becomes it": `determineFileSizeIndex` tests the current index, not the
    result (`FileStream.java:964-966`), so one jump past 2·10^9 is
    possible; `setMax2G` is called only by `FileStream`'s tests.
11. **Omission, fixed (8.5, a paragraph "The key nodes' contents").**
    Section 8 says which index nodes a record holds and every number in
    the header and the lists, but not that the klongs and refs of each key
    node, and its splits, come from the Dag's algorithm, which it leaves
    to the port without saying so: the capacity tests (`size + 1 <
    maxNodeSize`, `size + n + 1 > maxNodeSize`), `KeyNode.lastVersion`
    (sorted, one live klong per compare value), the split rule (`last.size
    > maxNodeSize / 2`), `firstAndSecond`'s split point, the in-place
    changes of a node made by the same transaction, `replaceKlong`, and
    the cut back of a replaced node (`Dag.java:616-1200`,
    `KeyNode.java:801-1270`). Added as a pointer, not a description.
12. **Omission, fixed (8.13, step 2).** "or at the end (`eod`)":
    `Dag.getMany` calls `eod()` only when the scan runs out of pairs
    (`Dag.java:569-596`), not after `ADD_AND_STOP`; so a step whose count
    stops at the last pair is not the last: the next step scans nothing,
    touches to the end and ends the iteration, one record more. A writer
    that sets the end when the last key is reached writes one record
    fewer.
13. **Minor, a sentence added (10.4, D2).** D2, the pointers below the
    physical first position, decides more for C than for two Java runs:
    C cuts at its own points (C2), so its first position differs from
    Java's after every cut. Left as a doubt; 012-05's sets with reclaim
    test it from the decided cut.
14. **Minor, fixed (8.14).** "A start appends nothing to the stream but
    recovery's fill": also the creation, on an empty stream; and a start
    may make a physical cut (`initFromDb`), which deletes files only.
15. **Minor, fixed (4.4; from 012-06, through the conductor).** With all
    four size bytes of a torn record present, a size of 5 to 16, which
    only a corrupt size field gives, passes recovery (5 left whole, 6 to
    16 filled) and the start's walk refuses it (below 17). Checked in
    `fixLastTransactionIfNeeded` and `transHeaderFixBytes`
    (`RecoverableStream.java:229-302`): a torn size of 1 to 3 bytes is
    completed to 17 or more.
16. **Minor, fixed (9.5 and 6.1; from 012-06, through the conductor).**
    `stringToIndex` parses with `Long.parseLong`, which takes a leading
    `+` and Unicode decimal digits (checked with a one-line program:
    `+6`, `٦` and `６` give 6), and `checkDbFiles` checks file by file in
    name order (name, first position, size), so the first failing check
    gives the message (`FileStream.java:736-784`); and `StoredTrans.Parser`
    refuses no negative node size (005-74), said in 6.1. 012-06's third
    point, the ordinal test that cannot fail, is finding 5.
17. **Minor, fixed (12).** "a pointer is printed `decimal/0xhex`": the
    hex is `Long.toHexString`'s (no leading zeros), and a negative
    pointer other than −1 prints as its two's complement
    (`StreamScan.ptr`); only a corrupt stream has one, but C's scanner
    prints the same text for the planted copies too.
18. **Minor, fixed (11, items 14 and 15).** Section 11 lists the
    differences of the format classes' comments from the code, but not
    `Klong`'s "First byte is stored in bits 6:3-7:2" (`Klong.java:36-38`;
    the code: bits 54 to 61, `Klong.java:150-164`), nor three smaller
    ones (`StoredKeyNode.java:66`, `Spos.java:17-19`,
    `RecoverableStream.java:64-69`).
19. **Minor, a sentence added (8.8).** "A port reproduces the record
    rule's result: the latest version": true of the model; Java gets it
    from what each pointer holds (Rule R's map of the last start's
    section, the canonical object, `writtenPos`), and its audit checks the
    equivalence only for the pointees its oracle knows (`Audit`'s INV-SLOT:
    "a pointee written before the startup section of the last startup is
    not known to it and not checked"). The sentence now says that a port
    computes it the same way; a table of every node's latest position would
    grow with the database. A matter of design for 012-07 and 012-09, so
    only noted.
20. **Omission, fixed (8.13, "At a start").** "`Reclaim.initFromDb`
    reads both keys back": how it combines them decides where the
    iteration in progress resumes: the current row replaces the table's
    row with the same `pStart` when neither is done, and the first
    available position and time come from the cut row with the largest
    `pStart` (`Reclaim.java:600-647`).
21. **Minor, fixed (4.5, last sentence).** "A stream of fewer than 128
    bytes that is not an incomplete creation is refused by
    `NodeStream.recover`": `Db.startInner` calls `refuseOtherNodeSize`
    first (`Db.java:678-680`), whose read of the block at 0 refuses such a
    stream, so `NodeStream.recover`'s check (`NodeStream.java:65-75`) is
    not reached. Probe `ReviewProbe short`: 3 bytes, `StreamIoException`
    ("Cannot read 6 bytes at position 0"); 60 bytes not "berg",
    `BadCryptoKey`; "berg" with version 1, `VersioningStreamException`;
    nothing written in any. It matters for the error that C's start gives
    (012-03's error enum, 012-14).

## 15.3 The audit and its findings C1 to C4

The audit's list (10.2) was checked against a grep of the Core for hash
collections and their iteration, sorts, doubles, clocks and threads; no
use that reaches the bytes is missing or misjudged. The order of a row's
names (`StringMap`), the take's doubles and the dither, and reclaim's two
conversions are as 10.2 says. Finding 1 (reclaim with a retain duration of
forever) is not a matter of determinism: Java's bytes are a function of
the inputs either way, but a writer must know it.

C1 to C4 hold, from the code:

* **C1** (005-72, as related): `determineFileSizeIndexFromFiles`
  (`FileStream.java:715-734`) gives the reopened last file a capacity
  from the larger of the last two files' lengths, so a restart can change
  the layout from there on; 9.2's rule gave the layout of the directories
  without restarts exactly (15.1).
* **C2** (005-72): `applyFileSizeChangeRules` (`:924-928`) sizes a new
  file from `length − getFirstPos()`, and the first position moves when
  `Reclaim.cutIfDurable` (`Reclaim.java:369-374`) makes the cut, at the
  first user transaction at which `getDurableLength()` has reached the
  decision's length: timing.
* **C3** (005-71): `DbClock` starts `lastReadTime` at 0
  (`DbClock.java:51-59`), and a start sets only `lastTransactionTime`
  (`setLastTransTime`, `:159-162`).
* **C4** (005-70): `Db`'s constructor makes a new `KeyModSet`
  (`Db.java:232`), whose first bin has `firstTime` −1 and no entry
  (`KeyModSet.java:115-126`); `modifiedAfter` (`:51-87`) then finds
  neither a conflict nor "too old" for any read time.

## 15.4 The result

21 findings: 2 errors (1, 2), 5 omissions (4, 9, 11, 12, 20), 14 minor. All
are fixed in the document; 13 and 19 are matters of judgement, noted with
a sentence and left as they were in substance. The errors: reclaim goes on
with an iteration in progress when the retain duration is forever (8.1,
8.13), and a leaf's key klong never names a delete node (6.3.1). Nothing
in sections 3 to 6 was wrong in its bytes; the tables lacked some of the
start's checks (finding 4). The take (8.7), the record's index nodes and
their order, the got-dirty positions, `prevPos`, `topPos`, `lastTrans`,
the table's text and the files' sizes were replayed independently from the
scans and agree with the document.

## 15.5 Progress

* 16:22: started; read 012-01 (sections 1 to 3, 6.2) and this document in
  full. Read so far against it: `MetaBlock`, `RecoverableStream`,
  `NodeStream`, `StoredTrans`, `StoredTopNode`, `StoredKeyNode`,
  `StoredValueNode`, `NodeChecksum`, `Spos`, `TransSeq`, `TransNodes`,
  `DbHelper.handleStillDirtyNodes`, `TopDs`, `TopNode`, `DatabaseId`,
  `DbBuilder`, and `Db` (constructor, `setStartupDistance`, the start,
  the creation, marking, `execute`, `store`, `putKvs`, `touchRange`).
* 16:43: findings 1 to 10 written and fixed in the document (committed).
  Then `Reclaim`, `DbStarter`, `Dag`, `KeyNode`, `FileStream`,
  `StreamScan` and the 2015 text read; the replay, the scans' checks and
  the probe `retain-forever` run (15.1).
* 16:48 to 17:00: findings 11 to 19; 012-06's three points, sent by the
  conductor at 16:50, checked against the code and added (findings 5,
  15, 16); 15.3 (C1 to C4) and 15.4 written. All committed.
* 17:00: the replay on the author's kept full set (278 workloads) found
  33 differences in `topPos` in one cut stream, `gen-18`: an artefact of
  the script, which forgot the newest top node written before its start
  in a cut stream; fixed (the script), 0 left there; the full set run
  again: 0 differences (15.1).
* 17:01 to 17:05: findings 20 (how a start restores reclaim's rows) and
  21 (a short stream is refused by the first read of a meta block; probe
  `short`); the klong checks on the full set; the tables' cells checked;
  the status line at the top updated. **Done**: every section read
  against the code; nothing left open but the doubts of 10.4 (D2 and D1
  are the ones that matter for C, findings 13 and 19) and Frans's
  questions Q1 and Q2. Java slips seen, for the conductor to register if
  wanted (not changed here): `KeyNode.checkIncreasingTime` never updates
  its `time` (finding 4); `StoredTopNode.parse`'s ordinal test cannot
  fail (finding 5); `NodeStream.recover`'s length check is unreachable
  from a start (finding 21); `Klong`'s and three other comments differ
  from the code (finding 18).
