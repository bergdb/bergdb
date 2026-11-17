005-40. Fix: a start writes to the stream before it checks the crypto key and the format
========================================================================================

Status: done (2026-10-25; see Outcome). Kind: fix. Created 2026-10-25.

Found on 2026-10-25 by Claude (Opus 5.5, Claude Code), from another
session's remark on `DbStarter.java:590`: "the stream format version isn't
checked at start. That's a missing check rather than wrong behaviour
today." At Frans's request: "Investigate this and propose what to do. If
you find it appropriate, add an item to 005." The probes, their runs on
`67bcc02` and a prototype of the fix are in
[40-fix-refused-start-writes/](40-fix-refused-start-writes/). No change to
`java/` then; fixed the same day, at Frans's request ("fix 005-40").


The format version is checked
-----------------------------

The line is a TODO in `DbStarter.validateTransactions`:

    // TODO D. check: t.version --- stream format version. We should check that this
    // software supports the version of the transactions in the stream.

It is older than the check it asks for. Frans wrote it on 2014-10-31, in
`DagStarter`, as a question ("t.version --- stream format version?
Check?"), when a record's header had four unused bytes. On 2015-07-24
(`bcebe1d`: "Only version 2 accepted when nodes / trans parsed") records
and nodes got a format byte, which their parsers check; on 2015-08-07 the
note became a "TODO D.", the last of Frans's priority letters A to D (the
original history: the f1 repository's F1-007,
`a/007-bergdb-261012/bergdb-git.bundle`). Since then the versions are
checked where they are read:

| Part | Version | Checked by | At start |
|---|---|---|---|
| Meta block | 154, bytes 4 and 5 | `RecoverableStream.readMetaBlock` | each meta block that recovery reads; `VersioningStreamException` |
| Record | 5, byte 4 (2 before 2026-10-15) | `StoredTrans.Parser.parse` | each record that startup parses: from the one that the last valid meta block names to the end, then the startup section; `StreamFormatException` |
| Key, top and value node | 2, 2 and 4, byte 5 | `StoredKeyNode`, `StoredTopNode` and `StoredValueNode.parse`, after the node's checksum | each node of those records, and later each node read; `StreamFormatException` |

`DbStarter` gets its transactions from the parser, so nothing is left for
it to check. The rule is Frans's of 2026-10-15 (F1-008-11's Q5): new
databases only, and a stream of the old format is refused with a clear
message. The meta block's version stayed 154 when the record format went
from 2 to 5.

The probes agree (`CrossVersion` and `FormatProbe format`, in
[runs/](40-fix-refused-start-writes/runs/) `cross.txt` and `format.txt`):

| A start on | The start | The stream after it |
|---|---|---|
| a database of the 2017 code (`0257e0b`, record format 2), by today's code | `StreamFormatException`: "Cannot parse stored transaction of format version 2; this version of BergDB reads format 5 only. A database written before 2026-10-15 (format 2) cannot be opened (docs/level2-alignment.md, M18)." | unchanged |
| a database of today's code, by the 2017 code | `StreamFormatException`: "Cannot parse stored transaction of format version 5." | unchanged |
| today's stream with format byte 6 in every record | the message of the first row, with 6 | unchanged |
| today's stream with version 155 in every meta block | `VersioningStreamException`: "Cannot read meta block with version 155. Version supported: 154" | unchanged |
| today's stream with format byte 5 in a value node, its checksum computed again | `StreamFormatException`: "Cannot parse value node of format version 5." | unchanged |

So the check is not missing. What the probes found instead is that the
start writes to the stream before it checks it, and that matters more
for the crypto key than for the format.


The fault: recovery writes first
--------------------------------

A start recovers an existing stream before it reads anything else from it
(`Db.startInner`, `NodeStream.recover()`, `RecoverableStream.recover()`):

1. `fixMetaBlockIfNeeded()`: if the stream ends inside a meta block, or
   (since 005-27) exactly where one starts, it appends the rest of one
   from `MetaBlock.FILL_OUT_TEMPLATE` ("berg", 154, then zeros: an invalid
   block).
2. `readLastValidMetaBlock()`: reads the meta blocks that are complete in
   the stream, from the last one back, and checks each one's magic bytes
   ("berg"; with a wrong crypto key they come out as others, which `Db`
   reports as `BadCryptoKey`) and its version.
3. `fixLastTransactionIfNeeded()`: zero-fills a torn last record.

So step 1 writes before step 2 has checked that the start can read the
stream. Its bytes go through the stream the start was given: with a wrong
crypto key they are encrypted with that key; without a key they are
written in plain text into an encrypted stream; with a key, into a stream
that is not encrypted, they are encrypted.

**A wrong crypto key.** `FormatProbe crypto` and `keys`: today's code, a
stream of 327,912 bytes with meta blocks at 0 and 200,000, cut x bytes
into the second one, as a crash can leave it. A start with a wrong key,
with none, or with one on a stream that is not encrypted, then a start as
it should be:

| x | The wrong start | Then the right start |
|---|---|---|
| 0 or 3 | `BadCryptoKey`; it appended 128 or 125 bytes | `BadCryptoKey`, at every start |
| 5 | the same; 123 bytes | `VersioningStreamException`: "Cannot read meta block with version 60826" (or 46234), at every start |
| 6 | the same; 122 bytes | starts, but for 5 of 2,560 wrong keys tried: "Meta block, bad last transaction spos" or "bad time", at every start |
| 50 or 127 | the same | starts (2,560 of 2,560 at each) |
| not cut, or the last record torn | `BadCryptoKey`; the stream unchanged | starts |

The right key reads the appended bytes as garbage: below x = 4 the
block's magic bytes, below 6 its version, and at any x its last byte,
which makes the block valid when it comes out as 10, 1 time in 256. Its
fields after x are then garbage too. With 2,560 keys that happened 5
times at each of x = 6, 50 and 127: at 6, each of the 5 failed, as the
block's time or last transaction was garbage; at 50 and 127 none did, as
the garbage then covers only reserved bytes (44 to 126) and the last
one.

Such a database is lost unless someone cuts the appended bytes off by
hand, and the message, "Likely, the wrong crypto key was used", sends its
owner looking for another key. It takes a crash that leaves the stream
ending at or just inside a meta block (005-27's case: a transaction that
ends where a meta block starts, and a crash between its two appends; or a
crash while a meta block is written), and then a start with a wrong key,
or with none, before the right one. That is rare, but it is what someone
does who tries keys after a crash. The 2017 code did the same from 1 to
127 bytes into a meta block (by its code); the fill at 0 bytes came with
005-27, and before it such a stream did not start at all.

**Another format.** The same order, with milder consequences today:

* A stream of another meta block version (155 in the probe) that ends
  inside a meta block is refused after the fill: 78 bytes at x = 50 (C6).
  Not cut, or cut in a record, it is refused unchanged, as the meta blocks
  are read before step 3 (C5, C7).
* A stream of another record format with a torn last record is refused
  after the zero fill: 10 bytes for 10 cut off (C3), and 1,117 for a
  header cut after 3 bytes, with byte 4 set to 4,
  `StoredTrans.CURRENT_FORMAT_VERSION` (C4). The 2017 code does the same
  to today's streams. That is harmless with the formats that exist: both
  frame records and meta blocks the same way and write the same bytes, and
  after it the right version starts (`CrossVersion` X4 and X5).

It would matter for a format that changes the framing (007-02 and
005-31's option B name two: a larger size field in the record, and
records continued in others): today's code could then damage a newer
stream before it refuses it, and a fill below x = 6 leaves version 154 in
a meta block of the newer format.

**The message.** A record of a format other than 5 gives a
`StreamFormatException` that names format 2 as the cause. That class is
for a stream that does not follow the format ("This should only happen if
the db stream was tampered with", says `validateTransactions`' Javadoc),
while `VersioningStreamException` was made for this case: "Typically, this
means that the stream was generated with a newer version of BergDB than
this one. Or, a very old version that is no longer supported by this
newer software." Only the meta block's check throws it. A database of a
newer BergDB would be reported as corrupt, or as written before
2026-10-15.


The fix, proposed
-----------------

1. **Read before writing.** `RecoverableStream.recover()` calls
   `readLastValidMetaBlock()` before `fixMetaBlockIfNeeded()`. It reads
   only meta blocks that are complete in the stream, and the block that
   the fill makes is invalid, so it finds the same block as now; but a
   stream that the start cannot read (a wrong key, none, a key on a
   stream that is not encrypted, another meta block version) is refused
   before anything is written. A prototype, one line moved
   ([prototype.diff](40-fix-refused-start-writes/prototype.diff)), on
   `67bcc02`: after each wrong start the stream is unchanged and the
   right start succeeds, also for the 2,560 keys at x = 6; the stream of
   version 155 cut in a meta block is refused unchanged; every other case
   as before. `before-commit.sh` passes, and `CrashTest` as `level2.sh`
   runs it, 25 rounds, has no failure
   ([runs/prototype-checks.txt](40-fix-refused-start-writes/runs/prototype-checks.txt)).
2. **Versions refused as versions.** The four checks of the records and
   nodes throw `VersioningStreamException`, as the meta block's does, and
   `VersioningStreamException` becomes a subclass of
   `StreamFormatException`, as `BadMagicBytes` and
   `StreamChecksumException` are, so that the code and the tests that
   catch `StreamFormatException` stay as they are. The record's message
   fits both ways, such as: "Cannot parse stored transaction of format
   version 6; this version of BergDB reads format 5 only. Format 2 is a
   database written before 2026-10-15 (docs/level2-alignment.md, M18); a
   larger number, one written by a newer BergDB."
3. **The rule for the next format change**, in comments at the version
   constants (`MetaBlock`, `StoredTrans.RECORD_FORMAT`, the nodes'
   `FORMAT_VERSION`): a change of the framing (a record's size field or
   last byte; the meta blocks' size, distance or layout) changes the meta
   block's version, which recovery then checks before it writes; a change
   of a record's header changes `RECORD_FORMAT`; of a node's layout, its
   format byte. New databases only (Q5). With the rule, the zero fill of a
   torn record before its format is read (C3, C4) stays harmless, as it
   uses the framing only, so the record's check need not move.
4. **The TODO and the constant.** The TODO at `DbStarter.java:590` goes,
   and a comment says where the versions are checked instead.
   `StoredTrans.CURRENT_FORMAT_VERSION`, 4, "was never the stored byte"
   (docs/log.md, 2026-10-15); `RecoverableStream` uses it only as the
   filler of byte 4 of a torn header. It becomes `RecoverableStream`'s
   own constant, with the same value, so that recovery writes the same
   bytes; with it goes the reference from `storage` to `core` that the
   "TODO D." at `RecoverableStream.java:15` asks to remove.
   docs/level2-alignment.md, 8.3, planned "one constant for both"; it was
   not done.

To decide with it, small: `MetaBlock`'s Javadoc says the version is an
int of 4 bytes, and `initBlock` writes it so, but it is read as 2 bytes
(`bytesToUShortLE`), so a version above 65,535 would be read wrong: read
the int, or document 2 bytes. `MetaBlock.VERSION_133` is unused.


Done when
---------

* Unit tests: a start with a wrong key, with none, and with a key on a
  stream that is not encrypted, on streams that end 0, 3 and 5 bytes into
  a meta block, throws `BadCryptoKey` and leaves the stream as it was,
  and a start with the right key then succeeds; a stream of meta block
  version 155 that ends inside a meta block is refused and left as it
  was; a record of format 6, and a node of another format, throw
  `VersioningStreamException`, and the message for format 6 does not name
  format 2 as its cause.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`; `java/stress/level2.sh`
  passes (its `CrashTest`, as recovery changes).
* The probes again, `tools/run.sh all`: no wrong start changes the stream.


Size and order
--------------

S: a line moved and its tests; four checks, a superclass and a message;
comments and a constant. Any time. 005-39, not committed when this was
written (it is `52d7e36`), changes another method of `RecoverableStream`
(`getPosOfTransCompletedBefore`); the two do not overlap. 005-33's option
A would add a check before recovery, for a creation that crashed;
independent of this one.


The probes
----------

In [40-fix-refused-start-writes/tools/](40-fix-refused-start-writes/tools/),
`run.sh` (build with `java/build.sh` first; `run.sh all` takes about 2
minutes on F53); their runs on `67bcc02` in
[runs/](40-fix-refused-start-writes/runs/), and after the fix in its
`after-*.txt` (`run.sh all after-`):

* `FormatProbe format` (`format.txt`): today's code, the core API, a
  `MemoryStream` whose version bytes are changed in place, C0 to C10.
* `FormatProbe crypto` (`crypto.txt`): a wrong key, none, and a key on a
  stream that is not encrypted, as written, with a torn last record, and
  cut 0, 3, 5 and 50 bytes into a meta block, K0 to K18.
* `FormatProbe keys 2560` (`keys.txt`): 2,560 wrong keys, each on its own
  copy, at cuts 6, 50 and 127 bytes into a meta block.
* `CrossVersion` (`cross.txt`): the 2017 code (`0257e0b`, which `run.sh`
  builds as 006-02 does) and today's, through the Pub API in directories,
  X0 to X5.
* The prototype: `prototype.diff`, and `prototype-format.txt`,
  `prototype-crypto.txt`, `prototype-keys.txt` and `prototype-checks.txt`.


Outcome
-------

2026-10-25, by Claude (Opus 5.5, Claude Code), as proposed, at Frans's
request ("fix 005-40"); in a clone, on `52d7e36`:

1. **Read before writing.** `RecoverableStream.recover()` reads the last
   valid meta block before `fixMetaBlockIfNeeded()`, so a stream whose meta
   blocks it cannot read (a wrong crypto key, none, a key on a stream that
   is not encrypted, another meta block version) is refused as it is, and
   so is one without any valid meta block. The Javadoc of
   `DatabaseBuilder.start()` says so for `BadCryptoKey`: the start has
   written nothing, and the right key can start the database.
2. **Versions refused as versions.** The checks of the records and of the
   key, top and value nodes throw `VersioningStreamException`, now a
   subclass of `StreamFormatException`, as `BadMagicBytes` is. The record's
   message (`StoredTrans.formatRefused`) says which BergDB wrote the
   stream: for format 6, "Cannot parse stored transaction of format version
   6; this version of BergDB reads format 5 only. A larger number is a
   database written by a newer version of BergDB."; for 2, that a smaller
   number is a database of an older version, which cannot be opened, and
   that format 2 was written until 2026-10-15.
3. **The rule**, in the Javadoc of `MetaBlock.CURRENT_VERSION` (the
   framing) and of `StoredTrans.RECORD_FORMAT` (what a record holds). One
   change from the proposal: a change of a node's layout changes
   `RECORD_FORMAT` too, not only the node's own byte, so that a start
   refuses such a stream at once. Startup parses at least one record, but
   not always a node of each kind.
4. **The TODO and the constant.** `DbStarter.validateTransactions` says
   where the versions are checked, instead of the TODO.
   `StoredTrans.CURRENT_FORMAT_VERSION` is gone, with its history in
   `RECORD_FORMAT`'s Javadoc; `RecoverableStream` writes the same filler,
   its own `TORN_HEADER_FILLER` (4), and no longer imports `bergdb.core`,
   so the "TODO D." about that is gone too. Two of its tests set byte 4 of
   a transaction to the constant before they cut it off; they no longer
   do. [docs/levels.md](../011-docs-archive/04-levels.md) has the fault as number 8 of
   "Bugs found by the load and crash tests".

Tests; the three of recovery fail without the fix (checked with the old
order in `recover()`: the stream grew by 128 bytes):

* `RecoverableStream.testRecoverWithWrongKeyWritesNothing`: streams cut 0,
  3, 5 and 50 bytes into the meta block at 200,000; a recovery with a wrong
  key, with none on an encrypted stream, and with one on a stream that is
  not encrypted throws `BadMagicBytes` and leaves the stream as it was; the
  stream as the right key reads it then recovers, with the transactions
  before the cut.
* `RecoverableStream.testRecoverOtherVersionWritesNothing`: meta blocks of
  version 155, cut 0, 3 and 50 bytes into one: `VersioningStreamException`,
  and the stream as it was.
* `PubTester.testWrongKeyAfterCrashAtMetaBlock`: an encrypted database
  through the Pub API, its stream cut where the meta block at 200,000
  starts; a start with a wrong key, and one without a key, throw
  `BadCryptoKey` and leave the stream as it was; then the right key starts
  it and reads the first value.
* `StoredTrans.testRefusesNewerFormat` (formats 6 and 200) and
  `testRefusesOldFormat` (2, now a `VersioningStreamException`); a
  `testRefusesOtherVersion` in each of `StoredKeyNode`, `StoredTopNode` and
  `StoredValueNode`.

Checks: `before-commit.sh`: BEFORE COMMIT OK (1,017 unit tests, 67
f-tests). `level2.sh`, in full: LEVEL 2 OK, its CrashTest 25 rounds without a
failure. StreamDigest against the
build before the change: DIGESTS IDENTICAL (36 of 36). The probes again
(runs/ `after-*.txt`): no wrong start changes the stream, and the right
key then starts, also for the 2,560 keys at 6 bytes into the meta block;
the versions of records and nodes are refused with
`VersioningStreamException` and the new messages, by today's code on the
2017 database too (X2, X4); all else as before, the zero fill of a torn
record of another format included (C3, C4), which the rule allows.

Not done, as proposed: the two points to decide, the meta block's
version read as 2 bytes of the 4 that the Javadoc names, and the unused
`MetaBlock.VERSION_133`.

Found on the way: `SalsaStream.getLength()` does not count what it
appends; its length is set once, when it is made (after appends of 150
bytes it says 0). BergDB itself is not affected: a `BufferedStream` is
always between, and it reads the length only before its first append. A
test or a tool that writes through a `SalsaStream` directly gets wrong
positions, as the first version of `testRecoverWithWrongKeyWritesNothing`
did. Not fixed.
