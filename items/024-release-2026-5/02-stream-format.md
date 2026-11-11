# 024-02. The stream format: the skeleton

Created 2026-11-11 by Frans Lundberg. Status: open.

The skeleton of a specification of BergDB's stream format, the first
work item of release 2026.5, written when its theme was "a stable stream
format" (Frans, 2026-11-10, 19:54). Since 2026-11-11 the theme of 2026.5
is "solid algorithms" (024-04) and the stable format is release 2026.6's
(026); this draft is kept current until then (024-04, section 5). Where
the text below says what 2026.5 decides for a stable format, read it with
that change. It lists every structure of the
stream, from the files to the bits, as numbered sections, so that the
full specification can be written section by section and checked against
the C clone. Each section says what it must define, which code defines it
today, which tests check it, which bits are unused or reserved, and where
the code accepts what a specification should refuse. Short and certain
content is filled in; the rest is marked **To be written**.

**Reference.** Release 2026.4: the tag `release-2026.4` (`bb8da6dc`),
record format 6. `main` at `4036bc1d` has the same `java/` but for
`BuildInfo.java`, so every line number here is one of the tag's and of
today's tree. The code was read, not changed or run.

**What it builds on.** 012-02 describes the stream byte for byte as Java
wrote it at `404d2ee` (2026-10-28), record format 5. No byte layout has
changed since: format 6 has the same fields and a new meaning of the
deletes in a record (section 8.2). What changed are the readers' checks
and the writer's rules; this document names them and cites 012-02 for the
rest. 012-02 is a description of the code; this skeleton is the outline of
a specification, which may refuse what the code accepts.


## 1. In short

* **The outline** (sections 3 to 17): the layers and their versions; the
  files; numbers, positions and alignment; the meta block; the framing
  and recovery; the record; the node header; the top node; the key node
  and its klongs; the value and delete nodes; keys; references and what
  a start reads; the internal keys; encryption; the Pub layer, as a
  pointer to its own specifications.
* **Filled**: the field tables of the meta block (6), the record (8), the
  node header (9), the top node (10), the key node and the klong types
  (11), the value and delete nodes (12); the file names and sizes (4); the
  internal keys and their texts (15); the version numbers and refusals
  (21.1). **To be written**: the writer's rules (what a record must hold:
  the take, the got-dirty list, format 6's tree rules), the start's rules
  in full (14), the directory rules, the encryption and Pub sections.
* **Gaps found** (section 19): 21 places where the code accepts what a
  specification should refuse, among them the time klong's bits 56 to 61
  (024's readme), a key klong's unused bits, the refs of time klongs,
  unchecked reserved bytes in every structure, the meta block's startup
  distance, a value node longer than its content, no checksum over a
  record's header; and 8 places where the result depends on Java rather
  than on the bytes, first among them the line order of reclaim's table,
  which is Java's `HashMap` order.
* **Open format questions** (section 20): 024-01's CL2, CL4, PF2, OT4,
  CA1, PA5 and PA9, with OT1 (c), CL1 and 017-08's checksums, and 13 more
  found here; for each, whether it can come later without a break or must
  be decided before the format is frozen.
* **Versioning** (section 21): what is versioned today, and four options
  for 2026.5's compatibility rule, none decided.
* **The C clone** is at 2026.4's candidate `03ce6ec5`, which writes
  format 5 (022's readme; `c/readme.md`, "Which Java"). Checking the
  specification against C needs C at the release first (024-01, CC1).


## 2. Reference, sources and conventions

**Sources.** 024's readme; 024-01, sections 4 to 11 and 15; 012-02,
sections 1 to 10; 020-07 (the object format), 020-10, section 4 (the
index keys), 020-22, section 4.1 (the internal key spaces), 020-28
(encryption out of the API); 017-08 (stream checksums) and 017-10
(encryption); 023-07, sections 5.1 to 5.8 (format 6's rules); the release
notes of 2026.4 (`releases/2026.4/readme.md`, "Format"); 022's readme and
`c/readme.md`. The code in `java/src/bergdb/` and `java/stress/`.

**Conventions**, as 012-02's:

* Integers are little-endian; `u8`, `u16`, `i32`, `i64`; `i32` and `i64`
  are two's complement.
* *pos* is a stream position, counting every byte, meta blocks included;
  *off* is an offset in a record's or a node's bytes.
* *SFE* is `bergdb.storage.StreamFormatException`, which
  `VersioningStreamException`, `BadMagicBytes` and
  `StreamChecksumException` extend. A *refusal* is an SFE (or a
  `DbException`) at a start or a read; a read that meets one fails the
  database.
* D = 200,000 and M = 128: the meta block distance and size.
* Code is cited as `Class.method` with its line in today's tree, in
  `java/src/bergdb/` unless another directory is named.

**The checks a section names.**

| Short | What                                      | Where                           |
|---|---|---|
| SD  | `StreamDigest`: SHA-256 of the stream     | `java/stress/StreamDigest.java` |
| CST | `CorruptStreamTester`: damage, then start | `core/CorruptStreamTester.java` |
| UT  | the parsers' own unit tests               | in each class, `@Nano`          |
| C   | the C clone's cross tests and vectors     | `items/022-bergdb-c/c/test/`    |
| FF  | `FormatFuzzer`, the Pub layer's readers   | `pubimp/FormatFuzzer.java`      |

SD compares builds and modes; it has no fixed digest in the code and
checks no refusal (the 48 digests of 2026.4 are in the release's
`baseline.zip` and in 023-09's folder). CST checks refusals and right
answers: after a cut, exactly the transactions before it; after other
damage, a refusal, a failed read, or a state the database had (its
Javadoc, lines 36 to 87, with its known blind spots: 015-73, 014-01,
019-30, 019-31, 019-33). C's cross tests compare streams byte for byte,
both scanners' output and both dumpers' refusals (`cross.sh`,
`writecheck.sh`, `corruptset.sh`); its vectors (`test/unit/vectors/`) are
the only pinned bytes, written by Java at format 5.

**Status words.** *Filled*: read off the code, short and certain.
*To be written*: the section's content, with the code to read named.
*To check*: a statement not yet confirmed in the code.


## 3. The layers and their version numbers

A stream is made of layers; each has its own code and, for some, its own
version number. From the bottom up:

| Layer                            | Code                                     | Section | Version  |
|---|---|---|---|
| The files of a directory         | `stream/FileStream`                      | 4       | none     |
| Encryption (not in 2026.4's API) | `stream/SalsaStream`                     | 16      | none     |
| The meta blocks, framing         | `storage/RecoverableStream`, `MetaBlock` | 6, 7    | meta 154 |
| The records                      | `core/StoredTrans`, `NodeStream`         | 8       | record 6 |
| The nodes                        | `core/Stored*Node`, `NodeChecksum`       | 9 to 12 | 2, 2, 4  |
| The tree a record means          | `dag/Dag`, `dag/KeyNode`, `DbStarter`    | 11, 14  | record 6 |
| The Core's internal keys         | `core/Reclaim`, `DbConstants`            | 15      | none     |
| The Pub layer's keys             | `pubimp/IndexKeys`, `PubKeys`            | 17      | none     |
| The Pub layer's objects          | `pubimp/ObjectFormat`, `pub/DbObject`    | 17      | 0x82     |

The five numbers in the stream (012-02, section 1, with 2026.4's values):

| Number             | Value | Where in the bytes       | Defined by                       |
|---|---|---|---|
| Meta block version | 154 | meta bytes 4 to 7, `i32` | `MetaBlock.CURRENT_VERSION`, :51 |
| Record format      | 6   | record byte 4 (`u8`)     | `StoredTrans.RECORD_FORMAT`, :59 |
| Top node format    | 2   | node byte 5              | `StoredTopNode.toLongs`, :203    |
| Key node format    | 2   | node byte 5              | `StoredKeyNode.toLongs`, :55     |
| Value node format  | 4   | node byte 5, both types  | `StoredValueNode.toBytes`, :222  |

What each covers, and how another value is refused, is section 21.1.
The internal keys' texts and the Pub layer's keys have no version of
their own; the object format has its header byte (17).


## 4. The stream's files

**Status: filled for the names and sizes; to be written for the rules a
reader applies, once it is decided whether they are part of the format.**

**Must define.** How a stream is stored in a directory: the file names,
which bytes each file holds, the sizes a writer may choose, what a reader
accepts, the lock file and other files, and what the cut does. Also
whether the file layout is part of the format at all: the bytes of the
stream do not depend on it (012-02, section 9.3, C1 and C2).

**Today** (`FileStream`'s class comment, :36 to :60; 012-02, section 9):

* A database's stream is in files `NNNNNNNNNNNNNN.bergdb`: 14 decimal
  digits, the file's first position divided by 100,000
  (`BYTES_PER_INDEX_UNIT`, :124; `indexToString`, :1141). The files hold
  the stream from its first position to its end, without gaps.
* Capacities (`FILE_SIZES`, :137): 200,000, 1, 5, 20, 100 and 500 MB, 2,
  10, 50 and 200 GB (decimal). A file is filled to its capacity before
  the next is made (`newFile`, :1230); the capacity is chosen by
  `applyFileSizeChangeRules` (:1268) when a file is made, and at an open
  by `determineFileSizeIndexFromFiles` (:1034), from the last two files'
  lengths (012-02, section 9.2).
* **The 2 GB limits.** Two different things. (1) `setMax2G` (:502), a
  setting off by default, keeps new files at 2·10^9 bytes or less, for
  file systems such as FAT32; it changes file sizes, not stream bytes, and
  nothing in the stream records it. (2) The record limit, 2^31 − 9 bytes,
  because a record's size field is an `i32` and Java serializes a record
  to one array (section 8.3).
* A stream with no append has no file (015-06): an empty or missing
  directory holds `bergdb.lock` only.
* `bergdb.lock` (`LOCK_NAME`, :150): a fixed 225-byte text (`LOCK_TEXT`,
  :156), never changed; the lock is an exclusive OS lock on one byte at
  2^62 (`LOCK_POS`, :153). `created.txt` is the Pub API's, outside the
  stream (`Db.writeCreatedTxt`, `core/Db.java`:1397): the creation date,
  the version that created it, the database id, and a crypto key line for
  an encrypted stream (16).
* The cut: `pretruncate` (:554) takes off every file that ends before
  reclaim's decided cut; the first position becomes a file boundary, a
  multiple of 100,000, at or before the cut; it always keeps the last
  file (015-31). Reads below the first position throw
  `ReadBelowFirstPosException`.
* Refused at an open (`handleExistingFiles`, :978; `checkDbFiles`,
  :1055): a name that is not a number from 0 to `Long.MAX_VALUE /
  100,000`; a file whose first position is not where the files before it
  end; a file other than the last whose length is not a multiple of
  100,000: `BadDirStateException`, an `IOException`, not an SFE. A
  directory locked by another stream: `DirectoryInUseException`.

**Tests.** UT: `FileStream`'s 46 tests (`testFileSizeRules0`,
`testRestartMissingFile`, `testPretruncate0`, `testLockFile`, ...). C:
`stream.c` ports the rules (`size_index_from_files`, `size_index`,
`open_dir`); `cross.sh` compares file names and sizes. SD compares the
bytes from the decided cut, not the files.

**Unused and reserved.** The lock file's bytes. `FileStream` ignores
every file but `*.bergdb`; the Pub API's start reads `created.txt`'s
crypto key line to refuse an encrypted database
(`DatabaseBuilderImp.refuseEncrypted`, `pubimp/DatabaseBuilderImp.java`:376;
section 16).

**Gaps.**

* G15. `stringToIndex` (:1163) strips leading zeros and parses with
  `Long.parseLong`, so a `+` sign, any number of leading zeros and other
  Unicode decimal digits are accepted: `+6.bergdb` and `٦.bergdb` are
  file 6 (012-02, section 9.5). Files are sorted by `String.compareTo`.
  A specification should accept exactly 14 ASCII digits, or say why not.
* J5. The layout depends on restarts (the open rule takes the last two
  files' lengths, C1) and on the moment of the physical cut, which is
  timing (C2). Two runs with the same bytes can have other files. The
  specification must say that a reader accepts any layout that the rules
  allow, or define the layout from the bytes alone.


## 5. Numbers, positions and alignment

**Status: filled from 012-02, section 2; unchanged since.**

**Must define.** Byte order; what a position counts; record bytes and
the mapping between them and positions; alignment; ids and vpos; times.

* **Byte order**: every integer little-endian.
* **Positions** (`spos`): from 0, every byte counted, meta blocks
  included. The cut does not change them; the first readable position is
  `AppendOnlyStream.getFirstPos()`. `Spos.NULL` is −1 (`dag/Spos`, :24).
* **Record bytes**: a record's own bytes, without the meta blocks inside
  it. Sizes and offsets in a record count record bytes. The position of
  record byte n of a record at p is `RecoverableStream.getSpos(p, n)`
  (:350); its inverse is `getStartSpos` (:373) (012-02, section 2.3, with
  the code). A byte that would fall at a multiple of D falls after the
  meta block there.
* **Alignment**: records start at multiples of 8 (`TRANS_ALIGNMENT`,
  `RecoverableStream`:72, `NodeStream`:26); a record's size is a multiple
  of 8; top and key nodes are multiples of 8 long, value and delete nodes
  multiples of 4. So `spos % 8` is 0 for a record, a top node or a key
  node, and 0 or 4 for a value node.
* **Ids and vpos**: a node's id is an `i64`, odd (a *vpos*, `Spos.isVpos`,
  :59), given in creation order from its record's position + 1; the
  creation's root key node has id 0 and its top node id 1 (012-02,
  section 2.5). An odd reference names a node not yet written; an even one
  a written version. Since format 6 the ids of a record can have gaps:
  the take-back drops a node made and emptied in one transaction, and its
  id stays used (`Dag.takeBack`, `dag/Dag.java`:1443; `DbStarter`,
  :402 to :410).
* **Times**: an `i64` in units of 100 ns since 1970-01-01 00:00 UTC
  (`Clock.UNITS_PER_SEC` = 10^7), from `Klong.MIN_TIME` = 0 to
  `Klong.MAX_TIME` = 2^56 − 1 (`dag/Klong`, :61 and :62), about the year
  2198. User transactions stop at `DbClock.LAST_USER_TIME` = MAX_TIME −
  1024 (015-55); internal ones go on to MAX_TIME.

**Gaps.** None in the bytes. The time's range, unit and epoch are frozen
with the format (Q20 in section 20).


## 6. The meta block

**Status: filled.**

**Must define.** Where meta blocks are, their 128 bytes, which values are
valid, which are refused, what a valid block is, and which fields a later
version may add.

A meta block is at every position k · D, k = 0, 1, 2, ..., and is M = 128
bytes long (`RecoverableStream.META_BLOCK_SIZE`, :59;
`META_BLOCK_DISTANCE`, :62). Layout (`MetaBlock`'s class comment, :14 to
:31):

| Off | Size | Type  | Field         | Value and range                                |
|---|---|---|---|---|
| 0   | 4  | bytes | magic         | `62 65 72 67`, "berg" (`MetaBlock.MAGIC`, :36) |
| 4   | 4  | `i32` | version       | 154                                            |
| 8   | 8  | `i64` | time          | the creation's time, in every block            |
| 16  | 8  | `i64` | lastTrans     | the last record appended before it, or −1      |
| 24  | 16 | bytes | database id   | 16 bytes, random (`DatabaseId`)                |
| 40  | 4  | `i32` | startup dist. | the setting in force, sd, in bytes             |
| 44  | 2  | `u16` | max node size | 8, 14, 30 or 62 (005-50)                       |
| 46  | 81 | zero  | reserved      | zero                                           |
| 127 | 1  | `u8`  | last byte     | 10: the block is valid                         |

**Written by.** `MetaBlock.initBlock` (:73): magic, version, last byte,
lastTrans −1. `Db.writePrimordialTransaction` (`Db.java`:1344): id,
startup distance, node size, time. `NodeStream.appendNodes`: lastTrans
after each record. `Db.setStartupDistance` (:541): the startup distance.
`RecoverableStream.append` writes the in-memory block, as it is, when the
record bytes reach a multiple of D (012-02, section 4.2). At a start,
recovery copies the last valid block whole, reserved bytes included
(`MetaBlock.setFromOtherMetaBlock`, :95).

**Checked on reading.**

* `RecoverableStream.readMetaBlock` (:707), for every block it reads,
  valid or not: the magic (`BadMagicBytes`, an SFE); the version as an
  `i32` (:724; bytes 6 and 7 checked since 019-01), not 154 a
  `VersioningStreamException`. It writes nothing before these checks
  (005-40).
* `MetaBlock.checkFormat` (:116), for a valid block: lastTrans below 0 and
  not −1, and a time below 0, are SFEs.
* `RecoverableStream.checkLastTransSpos` (:170, 019-34): lastTrans must
  be −1, or at least max(128, the first position) and below the block's
  own position; an SFE before recovery writes.
* `Db.refuseOtherNodeSize` (`Db.java`:1312), on the last valid block:
  0 is a `VersioningStreamException` (a database before 2026-10-27);
  another size than the start's is an SFE. Both before any write.

**Tests.** UT: `MetaBlock` (4), `RecoverableStream` (37, among them
`crashInMetaBlockHeader`, `testReadMetaBlock1`), `DbTesterRestart`
(`testMetaBlockLastTransPosRefused`, `testOtherNodeSizeRefused`,
`testNoNodeSizeRefused`, `testVersionHighBytesRefused`). CST's META
workload. C: `meta.c`, `rstream.c`, `t_rstream.c`.

**Unused and reserved.** Bytes 46 to 126, written zero, not checked, and
copied whole into the next blocks: the place where 005-50 added the node
size without a new version (`MetaBlock.CURRENT_VERSION`'s comment, :40 to
:50). A rule of extension already: an older reader ignores and passes on
a field added there.

**Gaps.**

* G7 (meta). The reserved bytes are not checked to be zero. That is what
  lets a later version add a field (above); the specification must choose
  between "ignored and copied" and "must be zero" per byte range (Q14).
* G8. A last byte other than 10 makes the block invalid, silently
  (`MetaBlock.isValid`, :252): 255 values mean "invalid", and only 0 is
  ever written (by recovery's fill, section 7).
* G9. The startup distance is not range-checked on reading (012-02, doubt
  D9; the C clone's take guards sd < 1); the builder refuses below 10 and
  `setStartupDistance` clamps to 400,000 to 10^9. The time is checked
  only to be 0 or more; the database id not at all.
* G19. The maximum node size is given by the start (`DbBuilder`,
  `maxNodeSize8()` to `maxNodeSize62()`) and compared with the block's,
  not taken from it: the Pub API always uses 30. A reader of the format
  could take it from the stream (Q19).
* The meta block has no checksum (017-08). Its validity is its last
  byte.


## 7. The framing and recovery

**Status: the frame is filled; recovery is to be written from 012-02,
sections 4.2 to 4.6, with 2026.4's changes below.**

**Must define.** The record frame that the framing layer knows (the size
field and the last byte), how records follow each other around the meta
blocks, the walk, what a reader does with a torn tail, and the fill that
recovery writes, byte for byte, since a second writer must write the same
bytes after a crash (012-02, section 4.4).

**The frame.** Records follow each other from position 128 without gaps;
the next is at `getSpos(pos, size)`. The framing layer knows two fields of
a record: bytes 0 to 3, its size in record bytes (`i32`); and its last
byte: 10 for a committed record (`RecoverableStream.LAST_BYTE`, :85), 0
for a failed one, made only by recovery's fill.

**Today's checks** (2026.4):

* The walk (`NodeStream.TransIterator.next`, :395 to :425): a size below
  17 (`RecoverableStream.MIN_TRANS_SIZE`, :69) is an SFE;
  `NodeStream.checkReadSize` (:245; 005-74, 021-14) refuses a size below 8
  and a record that does not end inside the stream; a last byte other than
  0 or 10 is an SFE ("Bad lastByte"); a record with last byte 0 is
  skipped, whatever its content.
* Recovery (`RecoverableStream.recover`, :127): the last valid meta block
  (`readLastValidMetaBlock`, :580); lastTrans checked (`checkLastTransSpos`,
  :170); a cut meta block completed from `FILL_OUT_TEMPLATE`
  (`fixMetaBlockIfNeeded`, :425); a cut record completed
  (`fixLastTransactionIfNeeded`, :256; `transHeaderFixBytes`, :296, with
  `TORN_HEADER_FILLER` 4, :81) and filled with zeros, its last byte 0.
* An incomplete creation, at most 264 bytes (`Db.CREATION_LENGTH`, :385):
  `RecoverableStream.isIncompleteCreation` (:199) and
  `Db.refuseIncompleteCreation` (:1290): `DatabaseNotCreatedException`,
  nothing written.
* The order of a start's checks: `Db.startInner` (:888), as 012-02,
  section 4.6, says.

**Tests.** UT: `RecoverableStream` (`testTransHeaderFixBytes*`,
`crashAtMetaBlockPosition`), `DbTester.testCrash8InCreation` (:1403, the
length of the creation, cut at every byte). CST: truncation at every byte
(its hard rule). C: `recover.c`, `t_recover.c`, `power.sh`, crash cuts in
`cross.sh`.

**Unused and reserved.** A failed record's content is not read: any
bytes between its size field and its last byte 0 are accepted.

**Gaps.**

* G18. Recovery writes its fill before the record format is read: a start
  that refuses a stream of another record format may first have appended
  the fill of a torn tail (`StoredTrans.RECORD_FORMAT`'s Javadoc, :37 to
  :58). The refusals of the meta version and the node size write nothing.
  The specification should say whether a refusing start may write (Q15).
* A size field of 5 to 16 with all four bytes present (damage) is filled
  as 012-02, section 4.4, says, and then refused by the walk: the fill is
  defined for bytes no writer writes. To be written as such.


## 8. The record

**Status: the header and the parts are filled; the writer's rules (which
nodes, in which order, the got-dirty list) are to be written.**

**Must define.** The record's fields and parts, its format number, its
size and limit, the padding, what a reader refuses, and what the record
means: which tree the start's rerun builds from it (section 14).

### 8.1. The layout

A record at a position that is a multiple of 8; offsets in record bytes
(`StoredTrans.Serializer.serializeHeader`, :751; `serializeNodes`, :767;
`serializeEnd`, :793; 012-02, section 5):

| Off | Size | Type  | Field           | Value and range                           |
|---|---|---|---|---|
| 0   | 4    | `i32` | size            | record bytes, a multiple of 8, 48 or more |
| 4   | 1    | `u8`  | format          | 6                                         |
| 5   | 3    | zero  | (unused)        | the upper bytes of the `i32` at 4         |
| 8   | 8    | `i64` | time            | the transaction's time tt, 0 to 2^56 − 1  |
| 16  | 8    | `i64` | startupPos      | 0, or a record's position at or before it |
| 24  | 8    | `i64` | topPos          | the newest written top node's position    |
| 32  |      |       | nodes           | top nodes, key nodes, value/delete nodes  |
| e   | 4    | `i32` | end of nodes    | 0                                         |
| e+4 | 4    | `i32` | got-dirty count | N                                         |
| e+8 | 16·N |       | got-dirty pairs | N pairs (id `i64`, position `i64`)        |
|     | 0–7  | zero  | padding         | so that the size is a multiple of 8       |
| s−1 | 1    | `u8`  | last byte       | 10                                        |

The padding is `computeZeroCount(n) = (8 − n % 8) % 8` (:274), n the
bytes up to and including the last byte. An empty record (no nodes, no
pairs) is 41 bytes and 7 zeros: 48.

**Checked on reading** (`StoredTrans.Parser.parse`, :314 to :417; `next`,
:423):

* tpos a multiple of 8 and 0 or more: else `IllegalArgumentException`,
  not an SFE (:324, :328).
* size 41 or more and within the buffer (:339); the format byte (:347,
  `formatRefused`, :236); room for the count and the last byte (:376);
  the count from 0 to (size − offset − 1) / 16 (:383); room for the
  padding (:401); a node size from 8 to what is left (:438); an end
  marker present (:425); and the content fills the size exactly (:410,
  015-72). Each an SFE.
* At a start, for the records it walks (`Db.getStartupPosFromLastTransaction`,
  :1000; `Db.checkStartupPos`, :1046, 015-75): startupPos not negative, a
  multiple of 8, 0 or at least 128, and not after the record.
* For the startup section (`DbStarter.validateTransactions`, :635):
  positions and times strictly increasing; times from 0 to 2^56 − 1
  (:664); each key node validated (section 11).
* topPos, of the last record only (`DbStarter.topNodeOfLastTransaction`,
  :305): a position, not −1 or a vpos, of the newest version of a top
  node (Rule R, :318 to :323, 015-75).
* A got-dirty pair whose id is not the node at its position: an SFE
  (`DbStarter.canonicalNode`, :494).

### 8.2. The format number, 6

Format 6 since 2026-11-10 (`70b4f788`; 023-07, section 5.8; 023-02, F9
(a)). The layout is format 5's; what changed is the meaning of a record's
deletes when a start reruns it, and so the tree the stream holds
(`StoredTrans.RECORD_FORMAT`'s Javadoc, :37 to :58; section 11.3):

* the upward unlink: a delete that empties its segment leaf does not
  write it, and unlinks each emptied node up to a stop node, which gets a
  delete bitmap (`Dag.deleteUpward`, :1095; `Dag.unlink`, :1400);
* the take-back: a node made by a split of the transaction and emptied by
  its delete is never written (`Dag.takeBack`, :1443);
* the empty key first: an inner node's smallest live klong is the empty
  key (`Dag.emptyKeyNext`, :1491; `KeyNode.firstAndSecond`, :1348);
* root collapse (`Dag.collapseRoot`, :1218; `takeBackRoot`, :1251);
* a space split in place of a segment root made by the transaction
  repoints the segment leaf's klong (`Dag.spaceSplitInPlace`, :1781;
  fault 12).

History: 2 until 2026-10-15; 5 from then (topPos in the header, 011-11,
M18) to 2026-11-10; 6 since. Format 6 is the only one 2026.4 reads.

### 8.3. The record limit

* `StoredTrans.MAX_RECORD_SIZE` = `Integer.MAX_VALUE` − 8 = 2^31 − 9
  (:66): the size field is an `i32` and a record is serialized to one
  Java array. The largest record is the largest multiple of 8 below it.
* The checks before the go point (`Db.checkSize`, user transactions only;
  `Db.checkDirtyNodes` with `Dag.dirtyNodeBound`): value nodes at most 7/8
  of the limit (`valueLimit`, :76), index nodes at most 15/16
  (`dirtyLimit`, :86).
* `recordLimit` (:69) is `static volatile`; tests lower it.

The limit is a writer's rule; a reader refuses only a size beyond the
stream or the buffer.

### 8.4. The parts and their order

* **Nodes**: the serializer writes the top nodes, then the key nodes,
  then the value and delete nodes (`serializeNodes`, :767). Each starts
  with its size; a node size of 0 ends them.
* **Value nodes' order**: in the order of the transaction's KVs: the
  builder's (`Trans.Builder.build`, a `TreeMap` in key order), or, when a
  key transformation ran, `Db.sortByKey` (`Db.java`:2998), one KV a key
  (023-08, section 7). The rerun applies them in stored order
  (`DbStarter.rerunTransaction`, :373).
* **The got-dirty list**: the index nodes that got dirty in this
  transaction and the record's nodes still dirty (012-02, section 8.6).
  **To be written**: its order and its rules, from `Db.store` and
  `TransNodes`.

**Tests.** UT: `StoredTrans` (22: `testCorruptRecordSize`,
`testCorruptGotDirtyCount`, `testRecordAboveLimit`,
`testRefusesOldFormat`, `testRefusesNewerFormat`), `DbTesterRestart` (six
refusals of header fields), `NodeStreamTester`. CST: header fields and
got-dirty entries. SD: every byte. C: `serial.c`, `strans.c`,
`t_records.c` with `records.txt` (359 one-change refusals, format 5).

**Unused and reserved.** Bytes 5 to 7, written zero, skipped (`offset +=
3`, :350). The padding, written zero, not read.

**Gaps.**

* G7 (record). Bytes 5 to 7 and the padding are not checked to be zero.
  017-08 and 019-07 propose a header checksum in bytes 5 to 7.
* G12. No checksum covers the 32-byte header or the got-dirty list
  (`Db.checkStartupPos`'s Javadoc; 017-08); the node checksums cover only
  the nodes. The parser accepts the nodes in any order of types (to check
  whether a start depends on the order); two value nodes of one key in one
  record are not refused (to check); startupPos is not checked to be
  non-decreasing from record to record, nor to be a record that the take
  reached (015-73).
* J4. The limit is Java's array limit, not a property of the bytes: a
  specification should state the largest size as a number, and whether a
  reader must accept every size up to it.


## 9. The node header and the checksum

**Status: filled.**

**Must define.** The 8 bytes every node begins with, the node types, the
checksum and when it is checked, and the size rules a reader applies.

| Off | Size | Type  | Field    | Value                                                 |
|---|---|---|---|---|
| 0 | 4 | `i32` | size     | the node's bytes, these 8 included                    |
| 4 | 1 | `u8`  | type     | 10 top, 20 key, 30 value, 40 delete (`dag/Node`, :35) |
| 5 | 1 | `u8`  | format   | 2, 2, 4, 4                                            |
| 6 | 2 | `u16` | checksum | Fletcher-16 of the node, bytes 6 and 7 counted as 0   |

**The checksum** (`NodeChecksum.sum`, :14 and :60;
`sumWithZeroReplace`, :34): sum1 and sum2 start at 0; for each byte b,
unsigned, in order, sum1 = (sum1 + b) mod 255 and sum2 = (sum1 + sum2)
mod 255; the result is sum1 | sum2 << 8, so byte 6 is sum1 and byte 7
sum2. Top and key nodes compute it over their longs, least significant
byte first, with bytes 6 and 7 zero; value nodes over their bytes with
the padding zeroed (012-02, section 6.1).

**Checked on reading** (`NodeStream.bytesToNode`, :271): the checksum
first (`checkChecksum`, :306: `StreamChecksumException`, an SFE), then the
type (another than 10, 20, 30 or 40: an SFE, :298), then the type's
parser, which checks the format byte (`VersioningStreamException`).
`NodeStream.readNode` (:197), which reads one node by a pointer's
position, refuses a position below 128 (019-32), a size of 6 or less, and
a node that does not end inside the stream (`checkReadSize`, :245).

**Tests.** UT: `NodeChecksum` (4, `testZeroReplace`). CST: node fields
changed with the checksum made right. C: `checksum.c`, `checksum.txt`.

**Unused and reserved.** Type values other than 10, 20, 30 and 40 (all
refused). Format values other than the type's one (refused).

**Gaps.**

* G13. Fletcher-16 modulo 255 does not see a byte changed from 0x00 to
  0xff or back (019-33, a known blind spot of CST), and passes about one
  random change in 65,025. A pointer that names a position inside a node
  or a record reads whatever bytes are there as a node; only the
  checksum, the type and the parser stand between them and a wrong node.
  A stronger checksum is 017-08's direction (Q12).
* `readNode` does not check that the node read has the type the pointer
  expects; its callers do: `NodeCollection.checkPointeeType` (:861;
  021-11), an SFE, when a pointer is followed (:513, :591, :633) and when
  a start links pointers (:733, :805; `DbStarter`, :252).


## 10. The top node

**Status: filled.**

**Must define.** The chain of top nodes: each points to the B-tree's
root key node of its time and to older top nodes by skip pointers; the
newest, the super root, is where a lookup starts (docs/sis-model.md,
section 6.3). Its layout, its ordinal and the skip pointers' rule.

Layout, 40 + 16·h bytes (`StoredTopNode`'s class comment, :24 to :30;
`toLongs`, :199; `parse`, :66):

| Off    | Size | Type  | Field        | Value and range                            |
|---|---|---|---|---|
| 0      | 8 |       | node header  | size 40 + 16·h, type 10, format 2          |
| 8      | 1 | `u8`  | h            | skip pointers: the ordinal's bit length    |
| 9      | 1 | zero  | (reserved)   | zero                                       |
| 10     | 6 | `u48` | ordinal      | 0 for the first top node, then + 1         |
| 16     | 8 | `i64` | id           | the node's id (section 5), not the ordinal |
| 24     | 8 | `i64` | root time    | the time of the transaction that made it   |
| 32     | 8 | `i64` | root pointer | the reference to the root key node         |
| 40+16i | 8 | `i64` | skip ptr i   | an older top node, or −1 when unset        |
| 48+16i | 8 | `i64` | skip time i  | that node's root time; −1 when unset       |

Skip pointer i is set exactly when bit i of the ordinal is (012-02,
section 6.2, with the rule of `TopDs.newSuperRoot`).

**Checked on reading** (`StoredTopNode.parse`): h read as a signed byte,
below 0 an SFE (:93); the size exactly 40 + 16·h and within the buffer
(:103); the format (`VersioningStreamException`); the root time from 0
to 2^56 − 1 (:123, :127); the root pointer 0 or more (:133); h equal to
the ordinal's bit length (:160); each skip pointer set exactly at the
ordinal's set bits (:167). At a start: topPos must name the newest
version of a top node (section 8.1).

**Writer's bound.** Ordinals are limited to 2^30 − 1 over a database's
life by `Db.refuseIfTopOrdinalsUsed` (`Db.java`:2443; item 002, M46);
the field holds 48 bits.

**Tests.** UT: `StoredTopNode` (9: `testRefusesOtherVersion`,
`testParserRefusesSlotsThatDoNotFit`, `testRefusesPointerCountBeyondTheNode`,
`testOrdinalField`). CST. C: `nwrite.c` (`nw_top_to_longs`), `snode.c`
(`sn_parse_top`), `top.txt`.

**Unused and reserved.** Byte 9. Values of h above 48 (refused through
the ordinal's check). The skip time of an unset pointer.

**Gaps.**

* G7 (top). Byte 9 is not checked (`offset += 1`, :107).
* G10. The skip times are not checked: an unset pointer's time is
  ignored, not required to be −1; a set pointer's time is not checked to
  be in the time range or to equal the root time of the node it names. A
  skip pointer counts as set when it is not −1, so −2 is "set" at parse
  and refused only when it is followed (`readNode`: below 128). The root
  pointer may be a vpos, a valid reference that Rule R resolves (14.1);
  whether Java's records ever hold one there: to check.


## 11. The key node and its klongs

**Status: the layout and the klong types are filled; the meaning of a
node's history and format 6's rules are to be written.**

**Must define.** A key node's layout; the klongs and their types, bit by
bit; what a node's klong array means (a history, read at a time); the
references; and the rules of format 6 that decide which nodes a record
holds (section 8.2).

### 11.1. The layout

32 + 16·n bytes (`StoredKeyNode.toLongs`, :51; `parse`, :87):

| Off      | Size | Type  | Field       | Value and range                              |
|---|---|---|---|---|
| 0        | 8 |       | node header | size 32 + 16·n, type 20, format 2            |
| 8        | 8 | `i64` | prevPos     | the version replaced: a position, a vpos, −1 |
| 16       | 1 | `u8`  | leaf        | 1 a segment leaf, 0 an inner node            |
| 17       | 2 | `i16` | n           | the number of klongs                         |
| 19       | 5 | zero  | (reserved)  | zero                                         |
| 24       | 8 | `i64` | id          | the node's id (section 5)                    |
| 32+8i    | 8 | `i64` | klong i     | i from 0 to n − 1 (11.2)                     |
| 32+8n+8i | 8 | `i64` | ref i       | klong i's reference (section 14.1), or −1    |

Java writes n as `sz << 8` in the third long, so bytes 17 to 19 hold n;
the parser reads bytes 17 and 18 as a signed `i16` (:132).

**Checked on reading** (`StoredKeyNode.parse`): size 32 or more and
within the buffer (:94); format 2; prevPos a position or −1
(`Spos.isValidOrNull`, :121); leaf 0 or 1 (:126); n not negative (:147)
and the size exactly 32 + 16·n (:153, 019-32); each klong's type 0, 1 or
3 (:175, 019-32); a key klong's ref a position or −1 (:179, 019-32).
At a start, for the startup section's key nodes and the versions it reads
from before it (`DbStarter.validateKeyNode`, :715;
`KeyNode.validateStreamNode`, `dag/KeyNode.java`:1762): n at least 1; time
klongs strictly increasing (`checkIncreasingTime`, :1707); a key klong's
ref a position, or −1 only after the startup time; before the section, no
time after the startup time (021-12).

### 11.2. Klongs

A klong is an `i64`; its type is bits 62 and 63 (`Klong`'s class comment,
`dag/Klong.java`:20 to :46; `getIntType`, :214):

| Type | Name          | Bits 0 to 61                                            |
|---|---|---|
| 0 | time          | the time in bits 0 to 55; bits 56 to 61 zero            |
| 1 | key           | a compare value: length in 3 to 5, bytes in 6 to 61     |
| 2 | (none)        | deprecated, never written, refused since 019-32         |
| 3 | delete bitmap | bit i set: klong i of this node is deleted from here on |

* **Time klong**: `createTime` (:105) asserts the time at most MAX_TIME;
  `getTime` (:178) masks bits 0 to 55. Klong's comment, since 2026.4:
  bits 56 to 61 "reserved and must be zero in stored times".
  `Klong.NULL` (:76), a marker in memory, is a time klong with bit 56 set.
* **Key klong**: a segment's compare value with bit 62 set
  (`createKey`; section 13): byte j of the segment (j = 0 to 6) in bits
  54 − 8j to 61 − 8j, the length (0 to 7) in bits 3 to 5, bits 0 to 2
  zero (once a version field, "no longer used"). Unused bytes are zero.
  `Klong.EMPTY_KEY` (:79), the empty key, is `0x4000000000000000`.
* **Delete bitmap**: 62 bits, one per klong index 0 to 61
  (`DELETE_BITS`, :88); a bitmap holds the bits of the node's bitmap
  before it and its own (`Dag.appendDeleteKlong`), and a reader applies
  the latest one it has read (012-02, section 6.3.1). A second delete in
  the same node by the same transaction changes that transaction's
  bitmap in place when it is the node's last klong.

### 11.3. What a node holds: to be written

**To be written**, from 012-02, section 6.3.1, and 023-07, sections 5.1
to 5.3, with the code of `Dag` and `KeyNode`:

* the history: a time klong begins the entries of its time; a later key
  klong with the same compare value replaces an earlier one; a reader at
  time t stops at the first time klong after t (`KeyNode.searchEq`,
  `searchLte`);
* the first klong is a time klong (a writer's rule; not refused, G6);
* in a segment leaf, a key klong of length 0 to 6 names a value node,
  never a delete node; one of length 7 names the root of the next
  segment's B-tree; in an inner node, a key klong names a child;
* **the empty key first** (format 6, 023-07, section 5.2, "LE-b"): an
  inner node's smallest live klong is `EMPTY_KEY`, and the empty key
  never gets a delete bit: a split's second half begins with it
  (`KeyNode.firstAndSecond`, :1348), and when the child it names empties,
  the next live child gets a new empty-key klong
  (`Dag.emptyKeyNext`, :1491);
* the stop node's delete bitmap of the upward unlink, root collapse and
  the take-back (section 8.2);
* the bound on n: at most the maximum node size, + 1 transiently
  (`KeyNode.check`, :1633), and at most 62 klongs that a bitmap can
  name.

**Tests.** UT: `StoredKeyNode` (`testRefusesKeyCountBeyondTheNode`,
`testRefusesBadKlongs`), `Klong` (18), `KeyNodeTester`
(`testNodeTextsSameInEveryRun` pins refusal texts), `DbStarter`
(`testParsedKeyNodeTimeOrder`, `testCheckStreamPointersOfKeyNode`). CST
(seed 20775 found G1). C: `nwrite.c` (`nw_key_to_longs`), `snode.c`
(`sn_parse_key`), `klong.c`, `knode.txt`, `klong.txt`.

**Unused and reserved.** Bytes 19 to 23. A time klong's bits 56 to 61.
A key klong's bits 0 to 2 and its bytes past its length. Klong type 2.
The ref of a time klong or a bitmap (written −1). Bitmap bits for
indexes n and above.

**Gaps.**

* G1. A time klong's bits 56 to 61 are not checked: `parse` checks the
  type only, and `getTime` masks them away. Found by CST's seed 20775: a
  start with -ea fails an assertion in `KeyNode.addKlong`; without -ea the
  database starts and answers right (024's readme). `Klong.NULL` is such
  a value. The fix proposed: "Bad time klong", an SFE, in `parse`.
* G2. A key klong's bits 0 to 2, and its data bytes past its length, are
  not checked in a key node. Such a klong compares as another value than
  the key it seems to hold. A value node's key checks bits 0 to 2, 62 and
  63, but not the bytes past a segment's length (section 12).
* G3. The ref of a time klong or of a delete bitmap, written −1, is not
  checked (`parse` checks a key klong's ref only, :178).
* G4. A delete bitmap's bits for indexes n and above, or for klongs that
  are not key klongs, are not checked.
* G5. n = 0 is refused only for the key nodes a start validates
  (`validateStreamNode`), not by `parse`; n above the maximum node size + 1
  is an assertion (`KeyNode.check`), not a refusal. `parse`'s test
  `size > Short.MAX_VALUE` (:133) cannot be true. Byte 19, the third byte
  of what Java writes as n, is not read.
* G6. That the first klong is a time klong is not checked. That time
  klongs increase is checked only by a start's validation (11.1), not
  when a node is read later (`addToEnd`, `dag/KeyNode.java`:1066, takes
  any order). That no time is after its record's time: to check.
* G7 (key). Bytes 19 to 23 are not checked (`offset += 5`, :139).


## 12. The value node and the delete node

**Status: filled.**

**Must define.** One KV of a transaction (type 30) or the deletion of a
key (type 40), written once, in its transaction's record. Its layout,
the stored offset, the key, the padding.

Layout (`StoredValueNode.toBytes`, :218; `parse`, :79; `getByteSize`):

| Off  | Size | Type  | Field       | Value and range                         |
|---|---|---|---|---|
| 0    | 8   |       | node header | size, type 30 or 40, format 4           |
| 8    | 8   | `i64` | id          | the node's id (section 5)               |
| 16   | 4   | `i32` | offset      | the node's offset in its record's bytes |
| 20   | 4   | `i32` | L           | the value's length (type 30 only)       |
| 24   | L   | bytes | value       | the value (type 30 only)                |
| 24+L | 4   | `i32` | key size    | 8·k, k ≥ 1 (at 20 for a delete)         |
| +4   | 8·k | `i64` | segments    | the key's k compare values (section 13) |
|      | 0–3 | zero  | padding     | to a multiple of 4; none for a delete   |

The size is 8 + 8 + 4 + 4 + L + 4 + 8·k for a value, 8 + 8 + 4 + 4 + 8·k
for a delete, rounded up to a multiple of 4. The stored offset is in
record bytes; the node's distance from its record's start in the stream
is longer by the meta blocks between them (005-34; 012-02, section 6.4).

**Checked on reading** (`StoredValueNode.parse`): size 24 or more and
within the buffer (:90); format 4; L from 0 to what is left less 4
(:125); the key size a positive multiple of 8 within the node (:139); the
key a key as `Keys.toSegments` makes it (`isKey`, :178: bits 0 to 2, 62
and 63 zero; every segment but the last of length 7, the last shorter;
:149); the offset one that `RecoverableStream.getStartSpos` accepts
(:158).

**Tests.** UT: `StoredValueNode` (8: `testRefusesSizesBeyondTheNode`,
`testRefusesBadKey`, `testOffsetFromTransAcrossMetaBlock`). CST. C:
`nwrite.c` (`nw_value_to_bytes`), `snode.c` (`sn_parse_value`).

**Unused and reserved.** The padding only.

**Gaps.**

* G11. The node size is not compared with the size its fields give: a
  node longer than its key and padding is accepted, and its extra bytes
  are not read. The padding is not checked to be zero. The stored offset
  is not compared with the node's real offset in its record, only checked
  to give some record position. A segment's bytes past its length are not
  checked to be zero (G2).
* Two value or delete nodes of one key in one record are not refused at
  parse (to check whether the rerun refuses them); since 023 a writer
  writes one a key (section 8.4).


## 13. Keys and segments

**Status: filled from 012-02, section 7; unchanged since.**

**Must define.** How a key, a byte string (a *bkey*), becomes segments
and compare values; their order; which keys exist.

* A bkey of length len is stored as k = len / 7 + 1 segments
  (`Keys.toSegments`, `dag/Keys.java`:240): segment i holds bytes 7i to
  7i + 6; every segment but the last has 7 bytes; the last has 0 to 6, so
  a key of 7·m bytes ends with an empty segment.
* A segment is a compare value (`Klong.createCompareValue`): byte j at
  bits 54 − 8j to 61 − 8j, the length at bits 3 to 5, bits 0 to 2 and
  62 to 63 zero. A key klong is its compare value with bit 62 set.
* Order: segment by segment as unsigned 64-bit numbers, a prefix first
  (`Keys.compareArrays`): the order of the bkeys' unsigned bytes.
* The Core takes any bkey, of any length from 0 (the empty key exists).
  The ikey encoding (each `/` as 1, every other UTF-8 byte + 2) is the
  Pub layer's and the internal keys' (`core/doc-files/key-encoding.md`,
  :153 to :172), not a rule of the stream.
* `Keys.hash` is in memory only.

**Tests.** UT: `Keys`, `Klong`. C: `klong.txt`; 012-02's `FormatFacts`
compared the order with the bytes' on 200,000 pairs.

**Gaps.** G2 (unused bytes of a segment). The stream has no limit on a
key's length but the record's.


## 14. References and what a start reads

**Status: the references and the outline of a start are filled; the
start's rules are to be written, from docs/sis-model.md, section 6.2, and
the code below.**

**Must define.** What a pointer stores; what a reader must do to read the
tree at a time; what a start reads, in which order, and what it refuses.
This is where a second implementation most needs words: the bytes alone
do not say that a reference may be older than the node's newest version,
or a vpos.

### 14.1. References

A reference (a key node's ref, a top node's root and skip pointers,
prevPos, startupPos, topPos, a got-dirty position, a meta block's
lastTrans) is an `i64`: a position, a vpos (odd: a node not yet written
when the reference was written), or −1. The writer's rule, the *record
rule* (`Handle.serializedRef`, `dag/Handle.java`:124; 009-02, section
4.6; 012-02, section 6.5): a value's position; the position of the node's
newest version if it is in memory; else the newer of the reference held
and the position this process last wrote. So a reference can name an
older version of its node, and a reader corrects it by Rule R. Within a
record every node's new position is set before any byte is written, so a
node can name a node written after it in the same record. A reference can
be below the stream's first position after a cut.

### 14.2. What a start reads

The outline (`Db.startInner`, :888; 012-02, sections 4.3, 4.6 and 8.14):

1. The checks before any write: an incomplete creation, the meta
   version, the node size (sections 6 and 7).
2. Recovery (section 7).
3. The startup position (`Db.handleStartParams`, :979;
   `getStartupPosFromLastTransaction`, :1000): from the record that the
   last valid meta block names (128 if none) to the end, every committed
   record parsed (so its format checked), its startupPos checked
   (`checkStartupPos`, :1046); the last one's startupPos is s.
4. The startup section (`Db.readTransactions`, :1067): every committed
   record from s (0 read as 128) to the end, parsed and validated
   (`DbStarter.validateTransactions`, :635).
5. `DbStarter` (`core/DbStarter.java`):
   * **Rule R**, reconciliation: `createMaps` (:144) maps each index
     node's id to its newest version in the section (`newById`), and each
     version's position, and each key node's prevPos, to its id
     (`posToId`); `updateStreamPointers` (:192) moves a pointer to the
     newest version when its node is known without a read (a vpos, or a
     position in `posToId`); `NodeCollection.resolvePointers` (:697) and
     `readVersion` (:583) apply Rule R to the rest when they are followed.
   * **The super root** from the last record's topPos
     (`topNodeOfLastTransaction`, :305), which must be the newest version
     of its top node.
   * **The rerun** of the section's transactions after the one at s
     (`rerunTransactions`, :358; `rerunTransaction`, :373), each at its own
     time, with the same ids, in stored order; and D, the dirty set, from
     the stored got-dirty pairs (`canonicalNode`, :494: the id must be the
     node at its position).
   * **Rule 4 by position** (`NodeCollection.linkToCanonical`, :771):
     each pointer of D's nodes linked to its node's canonical object by
     the pointer's position, through the section's versions and their
     prevPos, without reading the stream (005-57; proved in the Lean model,
     005-58, `Rule4Pos_handles`; after a cut, 005-62). With -ea,
     `checkLinkById` (:829) compares it with rule 4 by node id.
   * **prevPos**'s role: it maps the version a key node replaced to its
     id (`posToId`), so that rule 4 and Rule R find a node by an older
     position (a reference written before the section).
   * `checkStreamPointers` (:734): after Rule R and the cut back to the
     startup time, no key klong's ref in the newest versions is −1 or a
     vpos.
6. Reclaim's table, current row and settings (`Reclaim.initFromDb`,
   :762; section 15).

A descent or scan that comes back to a node it passed is an SFE
(`OpData.descentFrom`, `dag/OpData.java`:62, Brent's cycle check;
`4b36218a`).

**To be written**: the rules as a reader's algorithm, with the
invariants they rely on (INV-1: each node at most once in D;
docs/sis-model.md, section 8); what s may be (any record at or before
the last, or only one that the take wrote, 015-73); the bound of the
startup section (T3, 007-08), which is a writer's promise, not a
reader's check; what a start appends (nothing but the creation and
recovery's fill; 012-02, section 8.14).

**Tests.** UT: `DbStarter`, `TransSeq` (17), `DbTesterRestart`
(`testCorruptStartupPosRefused`). Level 2's scripts and the Lean
conformance (`java/stress/level2.sh`). CST (seeds 20767, 20769 and 20770:
`testFoundDescentCycle`, `testFoundLinkByIdPrevPos`). C: `starter.c`,
`transseq.c`, `ncoll.c`; `writecheck.sh take`.

**Gaps.**

* G14 and J3. Which checks are refusals and which are assertions depends
  on -ea: `checkLinkById` runs only with -ea; one of its outcomes is an
  SFE since `4df672f4`, every other an `AssertionError`. A time klong with
  bits 56 to 61 set (G1) fails an assertion with -ea and starts without
  it. The specification must say which conditions are refusals, so that
  they do not depend on how the JVM runs.
* G12 (start). startupPos is not shown to be a record that the take
  wrote (015-73); a damaged one that passes `checkStartupPos` gives
  another section.
* The C clone lacks the release night's two fixes (`4df672f4`, the
  prevPos refusal; `4b36218a`, the cycle check): C at `03ce6ec5`.


## 15. The internal keys

**Status: filled for the Core's keys and texts; the rules for the
reserved spaces are a pointer to 020-22.**

**Must define.** The keys that the Core writes in the key space, their
values' bytes, what a start reads from them and refuses; and which key
spaces are reserved, for whom.

The ikeys and their bkeys (`DbConstants.INTERNAL_PREFIX`, :21, "/#i/",
bkey `01 25 6b 01`; key-encoding.md, :153 to :172):

| Key                          | Written by                    | Value              |
|---|---|---|
| `/#i/-dummy`                 | `Db.setStartupDistance`, :569 | 200,000 zero bytes |
| `/#i/dreclaim/-table.txt`    | `Reclaim.storeTable`, :901    | the table's rows   |
| `/#i/dreclaim/-current.txt`  | a step's touch, `Reclaim`:653 | the current row    |
| `/#i/dreclaim/-settings.txt` | `Reclaim.setSettings`, :258   | two lines          |

* **`/#i/-dummy`** (`DbConstants.DUMMY_KEY`, :26): a value of
  `RecoverableStream.META_BLOCK_DISTANCE` zero bytes, so that a meta block
  with the new startup distance is written; never read.
* **A row** (`Reclaim.IterationInfo.serialize`, :1167): a `StringMap`,
  lines `name=value\n`, UTF-8 (`StringUtil.toBytes`), eleven names:
  pStart, pCut, tStart, tEnd, kvCount, lastKey, done, cut, rewritten,
  pEnd, pSafe. Numbers by `"" + long`; done and cut `true` or `false`;
  lastKey `null` or the segments as signed decimals separated by spaces.
  **No endKey**: P8 (024-01, CL1) was not taken.
* **The table** (`serialize`, :1356): the rows, each followed by
  `----next----\n`; parsed by `split` (:1376), and a table with no row is
  refused.
* **Reading a row** (`deserialize`, :1202; `StringMap.parse`,
  `common/StringMap.java`:33): lenient. Lines trimmed; lines without `=`
  skipped; names in any order; unknown names ignored; pStart, tStart,
  tEnd, kvCount, lastKey and done required; cut, rewritten, pEnd, pSafe
  and pCut have defaults.
* **The settings** (`serializeSettings`, :300; `parseSettings`, :314;
  015-87): exactly `retain=<long>\nfraction=<int>\n`; retain at least
  `Clock.UNITS_PER_SEC` (`Long.MAX_VALUE` is forever, the default without
  the KV), fraction from 66 to 58982 in units of 2^-16 (default 16384,
  :184, :191). Any other bytes are refused with `InternalDataException`
  ("Bad value of /#i/dreclaim/-settings.txt"), and the start fails
  (`initFromDb`, :762 to :769). Strict on purpose: "the settings of a later
  version, which this one must neither run without nor drop".
* **The reserved spaces** (020-22, section 4.1; key-encoding.md, :133 to
  :150): the Core's `/#i/dreclaim/` and `/#i/-dummy`; the Pub layer's
  `/#i/didef/`, `/#i/dient/`, `/#i/didel/` and `/#i/div/` (section 17);
  2026.3's `/#i/dii/` (a start refuses it) and `/#i/di/` (never read); the
  rest of `/#i/` and all of `/#` outside it reserved, used by nobody.
* The startup distance is not a KV: it is the meta block's (OT4).
* The creation writes no KV: its record is an empty root key node and
  the first top node (`Db.writePrimordialTransaction`, :1344; 012-02,
  section 8.2, with its 264 bytes).

**Tests.** UT: `DbTesterRestart` (554 to 867,
`testMalformedSettingsRefusedAtStart`, :817), `StringMap`. C:
`reclaim.c` (`rc_row_text`, `rc_settings_parse`), `strmap.c`,
`reclaim.txt`, `strmap.txt`.

**Gaps.**

* G16 and J1. A row's line order is Java's `HashMap` iteration order
  (`StringMap.serialize`, :101): pCut, tEnd, cut, pStart, tStart, lastKey,
  rewritten, pEnd, pSafe, done, kvCount, from `String.hashCode` and the
  JDK's `HashMap` since Java 8 (`c/src/strmap.h`, :1 to :20, copies it).
  The bytes of every reclaim record depend on it. J2: the numbers' text is
  `Long.toString`'s.
* G16 (reading). The row parser is lenient where the settings parser is
  strict: a row with a field of a later version is read, the field
  ignored, and dropped at the next store. The table's text has no version.
* G17. The Core accepts a user's puts under `/#` (024-01, CA3; C-U2-8),
  reclaim's keys included; a bad settings value stops the next start.
* The dummy's 200,000 bytes are a cost of keeping the startup distance in
  the meta block (Q4).


## 16. Encryption

**Status: what exists is filled; the specification's place for it is an
open question (PA9).**

**Must define.** Whether an encrypted stream is in the format, and if so:
how a reader tells that a stream is encrypted, which bytes are encrypted,
how the keystream is derived, and how integrity is checked.

**Today.** Encryption left 2026.4's API (020-28); the code stays, public
but internal (`stream/SalsaStream.java`, :16 to :21), reachable through
`DbBuilder.mainStream` (`core/DbBuilder.java`:295):

* `SalsaStream` sits under `RecoverableStream`, over `FileStream`
  (`pubimp/DatabaseBuilderImp.java`:499 to :504): it encrypts every byte
  of the files from position 0, meta blocks and magic included.
* The keystream is Salsa20/20 (`common/Salsa.java`): the key data's 40
  bytes give the nonce (bytes 0 to 7) and the key (8 to 39); the block
  counter is pos / 64; byte p is plain XOR keystream(p / 64)[p % 64]
  (`SalsaStream.read`, :143; `append`, :178). The nonce is fixed per key,
  not per database or start (U7-1, keystream reuse). No MAC (U7-3).
* Nothing in the stream says it is encrypted: only `created.txt`'s
  "crypto key" line, outside it. A wrong or missing key shows as bad magic
  bytes (`Db.startInner`, :898 to :918).
* The C clone has no encryption (`c/readme.md`, section 11).

**For the specification.** Format 6's specification covers the plain
stream; encryption is a transform under the framing. What a later design
needs from the format (017-10): a marker outside the encrypted bytes, a
nonce per database or per start stored in clear, and a place for
integrity (authenticated pages, or a MAC per record). Q11 in section 20.

**Gaps.** G20: no marker; a reader cannot tell an encrypted stream from
damage (020-28, :44 to :45).


## 17. The Pub layer on top: a pointer

**Decision: a pointer, not a section.** Why:

1. The Core is a key-value store of byte arrays and knows nothing of
   objects (010-01, P12). The stream's specification must be complete
   without the Pub layer: a reader of the Core, the C clone among them,
   never reads an object, and its tests do not need one.
2. The object format has its own specification, frozen at 2026.4, with
   its own version byte and its vectors: 020-07 (sections 4 and 9; the
   header 0x80 + version, so 0x82 for format 2, 0x83 to 0xbf reserved;
   `pubimp/ObjectFormat.java`:51; `pubimp/doc-files/object-vectors.txt`).
   Copying it here would make two texts to keep equal.
3. The Pub layer's keys (directories, index definitions, entries,
   markers) are a layer over the Core's keys, specified in 020-10,
   section 4, and 020-22, section 4.1; what this specification needs of
   them is the reservation of their key spaces (section 15).

**What the pointer must name**, a list to keep with the specification:

* Values: no type tag. A `byte[]` raw, a `String` as UTF-8, an object as
  format 2, at an object key only (`pubimp/RwEnvironmentImp.put`, :358);
  a read decides by the class asked for, the key's suffix and the first
  byte (`KvToObjectImp`, :66; `Entries.isProbablyDbObject`, :89).
* Keys: ukey to ikey ("d" before each directory name, "-" before the file
  name; `PubKeys.u2i`, :39); index definitions `/#i/didef/-NAME` (a format
  2 object with `version=1`), entries under `/#i/dient/`, markers under
  `/#i/didel/` (020-10, section 4; `IndexKeys`, `IndexDefinition`).
* What a Pub start reads and refuses: index data only
  (`IndexManager.start`, :148): a key under `/#i/dii/`, a bad
  definition or marker; no entry and no user value (020-10, section 4.5).

**Gaps.** G21: no Pub format version in the stream; a value's type comes
from its key and first byte (Q10).


## 18. Tests and checks

**Status: filled for what exists; what the specification needs is to be
decided.**

| Check           | Covers                          | Refusals | Pinned bytes | Runs          |
|---|---|---|---|---|
| Parsers' UT     | each structure, one change      | yes  | no           | before-commit |
| CST sample/full | damage, cuts, header fields     | yes  | no           | unit; night   |
| SD              | every byte, 12 configs, 4 modes | no   | outside code | by hand       |
| FF (`fuzz.sh`)  | the Pub layer's readers         | yes  | vectors      | night         |
| C `cross.sh`    | bytes, scans, dumps, crashes    | yes  | no           | C's gate      |
| C vectors       | records, klongs, nodes, texts   | yes  | format 5     | C's unit      |
| Level 2 to 4    | start, reclaim, eviction        | some | no           | by hand       |

* `StreamDigest` (`java/stress/StreamDigest.java`, :76 to :91 for the
  configurations): no Java test calls it; release checks compare the 48
  digests by hand (020-31, section 3).
* There is no golden stream in `java/`: `Db.CREATION_LENGTH` (264) and
  `DbTester.testCrash8InCreation` check the creation's length, not its
  bytes. The only pinned bytes are C's vectors, written by Java at format 5
  (`test/cross/java/Vectors.java`), and the creation's 264 bytes in
  012-02, section 8.2 (format 5).
* `StreamScan`, Java's scanner of 012-02, section 12, is no longer in
  `java/`; it lives in `c/test/cross/java/StreamScan.java`.

**What the specification needs** (to be decided, with section 21): vectors
of format 6 (one record of each kind, the creation's bytes), one refusal
vector per rule the specification adds (each G of section 19), and the
corpus of saved databases (024's readme) read by every later release.


## 19. What the code accepts that a specification should refuse

**Status: filled; a list for the specification's decisions.** Each place
is named in its section. G is a gap in the checks of bytes; J a place
where the result depends on Java rather than on the bytes.

| ID  | What is accepted, or depends on Java         | Section | Code                      |
|---|---|---|---|
| G1  | a time klong's bits 56 to 61 set             | 11      | `StoredKeyNode.parse`     |
| G2  | key klong bits 0 to 2; unused segment bytes  | 11, 12  | `parse`; `isKey`          |
| G3  | a time klong's or bitmap's ref not −1        | 11      | `StoredKeyNode.parse`     |
| G4  | bitmap bits for index n and up, or non-keys  | 11      | none                      |
| G5  | n = 0, or n above the node size, at parse    | 11      | `KeyNode.check`, :1633    |
| G6  | a first klong that is not a time klong       | 11      | `KeyNode.addToEnd`        |
| G7  | non-zero reserved bytes and padding          | 6 to 12 | the parsers' skips        |
| G8  | a meta last byte other than 0 and 10         | 6       | `MetaBlock.isValid`       |
| G9  | any startup distance; any database id        | 6       | `MetaBlock.checkFormat`   |
| G10 | top node skip times; −2 as a set pointer     | 10      | `StoredTopNode.parse`     |
| G11 | value node: extra bytes, its stored offset   | 12      | `StoredValueNode.parse`   |
| G12 | no header checksum; node order; startupPos   | 8, 14   | `StoredTrans.Parser`      |
| G13 | Fletcher-16 blind to 0x00 and 0xff           | 9       | `NodeChecksum`            |
| G14 | rule 4's checks only with -ea, as asserts    | 14      | `checkLinkById`, :829     |
| G15 | file names with `+`, other digits, zeros     | 4       | `stringToIndex`, :1163    |
| G16 | reclaim's row: any order, unknown names      | 15      | `StringMap.parse`, :33    |
| G17 | a user's puts under `/#`                     | 15      | `Trans.Builder` (CA3)     |
| G18 | a refusing start may write recovery's fill   | 7       | `Db.startInner`, :888     |
| G19 | the node size given by the start             | 6       | `refuseOtherNodeSize`     |
| G20 | nothing marks an encrypted stream            | 16      | `SalsaStream`             |
| G21 | no Pub format version in the stream          | 17      | the Pub layer             |
| J1  | a row's line order is `HashMap`'s            | 15      | `StringMap.serialize`     |
| J2  | `Long.toString` and `Long.parseLong` texts   | 4, 15   | `StringMap`, `FileStream` |
| J3  | -ea: refusals become assertions or go        | 14      | `checkLinkById`           |
| J4  | the record limit is Java's array limit       | 8       | `StoredTrans`, :66        |
| J5  | file sizes from restarts and cut timing      | 4       | `FileStream`, C1, C2      |
| J6  | an OS lock on byte 2^62 of `bergdb.lock`     | 4       | `FileStream`, :153        |
| J7  | a refusal known by Java's class and text     | all     | C compares (021-15)       |
| J8  | ranges of Java's signed types: h, n, formats | 8 to 11 | the parsers               |

J8 in detail: the top node's h is read as a signed byte, so h of 128 or
more is refused as negative; a key node's n as a signed `i16`; the format
bytes are compared as signed bytes. The specification should give every
range as numbers, unsigned unless said otherwise.

**Already fixed in 2026.4** (not gaps any more; since 012-02's reference):
a record's size against its content (015-72); the meta version's bytes 6
and 7 (019-01); a key node's size against its count, its klong types and
its refs (019-32); a node position below 128 (019-32); a cycle in a
descent (`4b36218a`); a damaged prevPos under rule 4, with -ea
(`4df672f4`); strictly increasing record positions and times, and time
klongs (005-75).


## 20. Open format questions

**Status: the list; nothing decided.** Each question names the structure
it touches and whether it can come later without a break. *Later,
additive*: a reader of today's format reads streams with it, or a refusal
of bytes that no writer writes. *Later, versioned*: it needs a new number
(record, node or meta), so a later release reads it only under the rule of
section 21. *Before the freeze*: it decides what the frozen bytes mean or
which bytes stay free, so it cannot wait.

| ID  | Question                                       | Structure            | Later?             |
|---|---|---|---|
| Q1  | CL2: strict shape, merges (MG) or RB           | rerun of deletes     | versioned          |
| Q2  | CL4: dead klongs in live nodes, compaction     | rerun, key nodes     | versioned          |
| Q3  | PF2: a compact key node; delta writes          | key node, node types | versioned          |
| Q4  | OT4: the startup distance in a KV              | meta 40 to 43, keys  | before the freeze  |
| Q5  | CA1: the builder's last operation wins         | a record's KVs       | later, writer only |
| Q6  | PA5: objects and what a key holds              | Pub keys, `/#i/`     | reserve now        |
| Q7  | OT1 (c): a clean stop's mark; the length       | a KV or the framing  | later, as a KV     |
| Q8  | CL1: P8, a reclaim row with E                  | reclaim's row text   | needs Q9           |
| Q9  | the internal texts: order, version, strictness | `/#i/dreclaim/`      | before the freeze  |
| Q10 | a Pub format version in the stream             | an internal KV       | before the freeze  |
| Q11 | PA9: encryption, its marker, nonce, MAC        | under the framing    | its place before   |
| Q12 | 017-08: checksums of header, meta block, link  | record 5 to 7, meta  | before the freeze  |
| Q13 | the must-be-zero checks (G1 to G4, G11)        | klongs, nodes        | later, additive    |
| Q14 | reserved bytes: ignored and copied, or zero    | every structure      | before the freeze  |
| Q15 | a start that refuses writes nothing            | recovery, versions   | later, additive    |
| Q16 | an unknown node type or format: refuse, skip   | node header          | before the freeze  |
| Q17 | the file layout: part of the format or not     | the directory        | before the freeze  |
| Q18 | the constants and ranges as numbers            | D, M, limits, signs  | before the freeze  |
| Q19 | the node size taken from the stream            | meta 44 and 45       | later, additive    |
| Q20 | the time: 100 ns, 1970, 56 bits, to ~2198      | every time field     | before the freeze  |
| Q21 | every check a refusal, with or without -ea     | the start's rules    | later, additive    |
| Q22 | one node a key and the node order, refused     | a record's nodes     | later, additive    |
| Q23 | startupPos: non-decreasing, a taken record     | record header        | later, additive    |

**Q1 to Q8, from 024-01:**

* **Q1, CL2** (024-01, section 4.2). Merges at the delete (MG), or reclaim
  rebuilds what it rewrites (RB). Either changes what a record's deletes
  mean to the rerun, so a new record format. Later only if the
  compatibility rule keeps each format's rerun path, switched by each
  record's format byte (option V-B, 21.3), as review C proposed and 024's
  readme plans ("switched on by the record's format"); else it must be in
  the frozen format or never.
* **Q2, CL4** (4.4). Compaction at the delete (DC) changes the rerun as
  Q1; RB with Q1. The same answer.
* **Q3, PF2** (9.2). A compact key node encoding (about 35 to 40 % fewer
  index bytes, estimated) is a key node format 3; delta writes a new node
  type with chains to read. Later if the rule lets a reader take several
  node formats (each node carries its format byte today); what a reader
  does with a format or type it does not know is Q16, which must be
  decided first.
* **Q4, OT4** (11.4). The startup distance out of the meta block into an
  internal KV (Frans, 2026-11-05: the meta block is for what cannot be
  stored otherwise). Additive in a way (a KV that wins, the field kept),
  but that leaves two places and the 200,000-byte dummy KV
  (`/#i/-dummy`, section 15) that forces a meta block. Before the freeze,
  to have one place.
* **Q5, CA1** (5.1). The last operation wins, put or delete. A writer's
  rule: no reader changes, since the rerun takes the stored nodes in
  order; other bytes for some Core transactions (SD, C). Any time. Whether
  "one node a key in a record" becomes a reader's rule is Q22.
* **Q6, PA5** (6.5). The Pub layer's questions; for the format, only the
  reservation of key spaces (020-22, section 4.1: the rest of `/#i/` and
  of `/#`). Reserve now; the features later.
* **Q7, OT1 (c)** (11.1). A clean stop's mark, so a start can tell a lost
  or cut last file from a torn tail. As an internal KV, later and
  additive; as a record kind of the framing, before the freeze. With it:
  checksums (Q12).
* **Q8, CL1** (4.1). P8 needs reclaim's row to hold E, the last key live
  when an iteration began (023-07, 5.13). Today's row reader ignores an
  unknown name and drops it at the next store (G16), so an older reader
  would run such a row wrongly without a word. It needs Q9 first.

**Q9 to Q23.** Q11 is 024-01's PA9 and Q12 is 017-08's; the others are
found here:

* **Q9.** Reclaim's texts: a fixed line order instead of Java's `HashMap`
  order (J1; a byte change, SD and C), a version or a strict parser as the
  settings have, and whether a binary form is better. Before the freeze:
  these KVs are in every database.
* **Q10.** A Pub format version in the stream, for example an internal
  KV written at creation; without one a reader cannot refuse a database of
  a newer Pub layer (G21). Before the freeze, if the Pub layer is under
  the same rule (21.3).
* **Q11, PA9** (6.9; 017-10). The feature is not for 2026.5, but its
  place is: a marker outside the encrypted bytes, a nonce per database
  stored in clear, and room for a MAC per record or per page. Today's
  `SalsaStream` encrypts the meta blocks too, so the marker cannot be in
  them. Decide the place before the freeze.
* **Q12** (017-08). A checksum of the record's header and got-dirty list
  (019-07: in bytes 5 to 7), a link from each record to the one before, a
  checksum of the meta block, a stronger node checksum. Each uses bytes
  that the freeze fixes: before the freeze, or reserve the bytes for it.
* **Q13.** Refusals of bits that must be zero (G1 to G4, G11's padding and
  extra bytes). No writer writes them, so a refusal breaks no database
  that a writer wrote: later and additive, if those bits are declared
  "must be zero" now and not kept for later fields (Q14).
* **Q14.** For each reserved range (meta 46 to 126, record 5 to 7, top
  node byte 9, key node 19 to 23, paddings): "ignored and copied", which
  lets a later release add a field without a new number (005-50's way), or
  "must be zero, refused", which makes every addition a new number. Before
  the freeze.
* **Q15.** A start that refuses a stream writes nothing, recovery's fill
  included (G18). Later and additive (the order of the checks).
* **Q16.** A node type, node format or klong type that a reader does not
  know: refused, as today, or skipped. It decides whether Q3 can come
  without a new record format. Before the freeze.
* **Q17.** The file layout: whether names and sizes are part of the
  format (G15, J5), and the name grammar (14 ASCII digits). 005-72 chose
  not to make the layout a function of the stream (2026-11-05, "Drop B";
  012-02, section 13, Q1). Before the freeze, as the C clone and any tool
  depend on it.
* **Q18.** The constants as numbers that do not move: D = 200,000, M =
  128, the alignments, the file unit 100,000, the record limit 2^31 − 9,
  the node sizes 8, 14, 30 and 62; every range unsigned unless said (J4,
  J8).
* **Q19.** The maximum node size read from the stream, so that a start
  need not be told (G19). An API change, no byte change.
* **Q20.** The time: 100 ns since 1970-01-01 UTC, 56 bits, so until about
  the year 2198. Frozen with the format.
* **Q21.** Every check a refusal, independent of -ea (G14, J3). Later and
  additive.
* **Q22.** A record's nodes in their order (top, key, value) and one value
  or delete node a key, refused otherwise (G12). Later and additive, if no
  writer writes otherwise (CA1 makes it so for the builder).
* **Q23.** startupPos non-decreasing from record to record, and a record
  that the take reached (015-73). Later and additive for the first; the
  second needs a way to tell, maybe Q12's link.


## 21. Versioning and compatibility

**Status: what exists is filled; the options are written; nothing is
decided.**

### 21.1. What is versioned today

| Number or mark       | Covers                             | Refused by, and when           |
|---|---|---|
| meta version 154     | the framing                        | `readMetaBlock`; before writes |
| meta node size ≠ 0   | databases since 2026-10-27         | `refuseOtherNodeSize`; before  |
| record format 6      | header, nodes, the rerun's meaning | `Parser.parse`; after recovery |
| node formats 2, 2, 4 | each node's layout                 | each parser, at a parse        |
| object header 0x82   | the Pub layer's objects (020-07)   | `ObjectFormat`, at a read      |
| index def. version=1 | an index definition (020-10)       | `IndexManager.start`           |

* The refusals are `VersioningStreamException`s, an SFE. The record's
  message tells an older format from a newer one (`formatRefused`, :236):
  "format 5 was written by release 2026.3 and earlier ..., format 2 until
  2026-10-15".
* A start parses every record from the one the last valid meta block
  names to the end, and the startup section, so a stream of another
  record format is refused at its start; a record outside those is
  checked when it is read, and a read that meets another format fails the
  database.
* History: record format 2 until 2026-10-15, 5 until 2026-11-10, 6 since;
  meta 154 since 2015; the node size since 2026-10-27. Each change has
  refused all older databases ("new databases only", F1-008-11's Q5).
  2026.4 refuses 2026.1 to 2026.3 (023-02, F9 (a)); 2026.5 need not open
  2026.4's (Frans, 2026-11-10, 19:49).
* Not versioned: the file layout, the internal keys' texts (the settings
  are strict and refuse a later form; the rows are lenient and drop it),
  the Pub layer's keys and value encodings.

### 21.2. What the format already offers a rule

* Each record carries its format byte, and each node its own. A reader
  can tell, record by record, which rules apply: the base of a mixed
  stream.
* The meta block has a version for the framing and 81 reserved bytes that
  an older reader copies whole: 005-50 added a field there without a new
  number (`MetaBlock.CURRENT_VERSION`'s comment, :40 to :50).
* The messages tell older from newer.

### 21.3. The options for 2026.5's rule

None is decided. Each says what a release reads and writes.

* **V-A. One format a release** (today). A release reads only the format
  it writes; every change of format refuses all older databases; a user
  re-creates the database, reading with the old release and putting with
  the new (2026.4's notes). Simple; no old code kept. It does not give a
  stable format by itself: only a promise not to change it.
* **V-B. Each record carries its format; a release reads every stable
  format.** From the first stable format on, a release reads every record
  of every stable format and writes only its newest; a stream may mix
  formats, the old records before an upgrade and the new after; the rerun
  switches on each record's format (CL2's way). Old databases open
  without a copy. Cost: every stable format's parser and rerun path kept
  for good, and tested on the corpus.
* **V-C. A database's format fixed at its creation.** The format in the
  meta block's reserved bytes or in the creation's record; a release reads
  every stable format and writes a database in its own format, or opens an
  older one read-only, with a tool that copies it to the new format. No
  mixed streams. Cost: old writers, or read-only paths and the tool.
* **V-D. Feature flags.** In the meta block's reserved bytes, three sets
  of flags, as some file systems' superblocks have: compatible (a reader
  may ignore), read-only compatible (a reader that does not know it opens
  read-only), incompatible (a reader that does not know it refuses). Each
  later addition (a checksum, merges, a compact node) is a flag, set only
  in databases that use it. It combines with V-B or V-C, and needs Q14
  answered as "ignored and copied" for the flag bytes.

For any option, to decide with it:

* what "stable" means: a format that a release promises to read, for
  how long (every later release, or a number of them);
* the first stable format: format 6 of 2026.4, or a format 7 of 2026.5
  after Q1 to Q23;
* a newer format met by an older release: refused, as today, with its
  message, or opened read-only (V-C, V-D);
* whether the internal keys' texts and the Pub layer are under the same
  rule (Q9, Q10), and the framing's meta version;
* the corpus (024's readme): databases saved by each release with a
  stable format, of the kinds that SD's configurations make (deletes,
  reclaim's cuts, large values across meta blocks, each node size, torn
  tails), with their digests, read by every later release: a night step,
  as `before-commit.sh` must stay fast.


## 22. How the specification is filled

* **Order.** The bytes first (sections 5, 6, 8.1, 9 to 13, mostly
  filled), then recovery's fill (7), the start's rules (14), the writer's
  rules that decide the bytes (8.4: the take, the got-dirty list, format
  6's tree; from 012-02, section 8, updated), the internal keys (15), the
  directory (4), and last the pointers (16, 17).
* **Checked against C.** C must first be at 2026.4 (024-01, CC1: the diff
  from `03ce6ec5` to the tag, format 6, the release night's two fixes);
  then each section's text is checked against C's code and its cross
  tests, and C's vectors are written again at format 6.
* **Decisions before code.** Section 19's gaps and section 20's questions
  are decided with Frans, in the order of section 21's rule first, then
  Q14 and Q16 (they decide which later changes are additive), then the
  rest; 2026.5's format changes are batched, so that C and SD change once
  (024-01, CC2).
* **Where it lives.** This subitem until the format is frozen. 012-01's
  D6b planned a `docs/stream-format.md`; a document in `docs/` is kept up
  to date with the code, which a frozen format's specification would be.
  Frans decides at the freeze.


## 23. Log

2026-11-11. Written 04:57 to 05:30, read only at `main` `4036bc1d`
(`java/` is `release-2026.4`'s but for `BuildInfo.java`); nothing built,
run or changed. From the code of 2026.4, 012-02 (format 5 at `404d2ee`)
and the items it cites; every line number cited was checked against the
code. Nothing decided. 024's readme does not yet list this file in its
Files section.
