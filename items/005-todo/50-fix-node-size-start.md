005-50. Fix the start with another node size
=============================================

Status: done (2026-10-27; see Outcome). Kind: fix. Created 2026-10-26.

Found in 005-38 ([report](38-writes-at-scale/report.md), section 6), by a
subagent (Claude, Opus 5.5) measuring node sizes; registered at Frans's
request (2026-10-26: "Yes to node-size fix entry. For now, it should fail
with a good error message. This should be the scope. Other options are
interesting, but later and in some other item.").

The fix proposed on 2026-10-27 by Claude (Opus 5.5, Claude Code), at
Frans's request ("Propose a solution were the node size is stored in the
MetaBlock."): the size in the meta block's reserved bytes, checked before
recovery writes. Decided by Frans the same morning (Decision), and made as
decided (Outcome). The probes and their runs are in
[50-fix-node-size-start/](50-fix-node-size-start/).


Decision
--------

2026-10-27, Frans, on the proposal: "No need to consider "today's
databases". There are none." And two questions: "Would StreamFormatException
be a good choice as an exception. Currently, we only really support node
size 30, and that is expected in the stream we open." "Why not use 1 or 2
bytes for the node size. We never test with larger sizes than 64, really."
Answered yes to both, with 2 bytes; then Frans: "Go ahead. If things turn
out ok, also implement this and commit the changes."

So the fix (below) differs from the proposal in three points:

1. A `StreamFormatException`, not a `DbException`. It is what a start
   throws for a stream that this BergDB does not read, beside
   `BadMagicBytes` and `VersioningStreamException`, its subclasses; no code
   on the start path catches it, and it is a `DbException`, as the Pub
   API's `DatabaseBuilder.start()` declares.
2. Two bytes, an unsigned short, not four: as `KeyNode.size`, a `short`,
   so the field never limits the size. The reserved bytes are 46 to 126.
3. A meta block without a size, 0, as in every database written before the
   fix, is refused like another size, with a `VersioningStreamException`
   (a stream of an older version of BergDB, which that class is for). The
   proposal started such a stream unchecked and recorded the size from its
   next meta block on; that line, its test and the cross-version case of it
   are gone.

[prototype.diff](50-fix-node-size-start/prototype.diff) is the proposal's
prototype, before the decision.


The issue
---------

A database starts only with the node size it was written with
(`DbBuilder.maxNodeSize8()`, `14()`, `30()`, `62()`; 30 by default). The
size is not in the stream. Started with another size, the rerun of the
startup section splits nodes differently, and the start fails with an
error that looks like a corrupt stream:

    StreamFormatException: startup error, node 1545529:1545529 not found,
    got dirty in trans tt=172, tpos=1545504; startup pos 1412496, time 174;
    in node table: no

All 12 pairs of 8, 14, 30 and 62 fail so; the same size starts and reads
every key back (`38-writes-at-scale/node-size/RestartNodeSize.java`, its
output `38-writes-at-scale/node-size/out/restart-check.txt`: 20,000 keys,
a startup section of about 1 MB). A startup section with no splits in it
might start, and then the database runs with the other size; not tested.
(Tested since: What the probes found, 2 and 3.)


The scope
---------

Only this: a start with another node size than the stream was written with
fails with a clear error, which says that the node size differs, both
sizes, and what to do (start with the size the database was written with).
Allowing a change of node size, or making the size a property of the
stream that the builder need not set, is not part of this entry (Frans:
"later and in some other item").


Questions
---------

1. Where the written size is kept. The meta block has 83 reserved bytes,
   zero (`MetaBlock`, offset 44): the node size there, with 0 for streams
   written before the fix, which then start as today. Or in a record.
   Which needs a new `MetaBlock` version (005-40's `VersioningStreamException`)
   and which does not?

   Decided: in the meta block, at offset 44, 2 bytes (Decision). It needs
   no new version: the code before the fix neither checks nor reads the
   reserved bytes and passes them on (The fix, point 2). A record could
   hold it in the three unused bytes of its header, also without a new
   format; but a start reaches a record only in recovery, which writes, or
   after it, and the size would be repeated in every record. The meta block
   is what a start reads first, and it holds the database's other
   constants, its ID and its startup distance. Streams written before the
   fix are refused (Decision, point 3).
2. The error's type: a new exception, or `DbException` with a message;
   what the Pub API (`DatabaseBuilder`) shows.

   Decided: a `StreamFormatException` with a message, and for a meta block
   without a size a `VersioningStreamException` (Decision). The Pub API
   shows the same exception: `DatabaseBuilder.start()` passes it on, under
   its `@throws DbException`.
3. Is a start with another size ever safe today (a startup section with no
   splits)? The fix refuses it anyway, if the size is known.

   No (What the probes found, 2 and 3). Such a start succeeds when the
   rerun of the startup section splits no node otherwise, as for a
   database just created or one with a single key. But with 20,000 keys
   and short startup sections, three such starts succeeded, read every key
   back, wrote more, and left a stream that no later start could open,
   with either size. Whether a start is of the harmless kind cannot be
   known before it is made.


What the probes found
---------------------

1. **The failure, confirmed (the first step).** 005-38's `RestartNodeSize`
   on `167597a` gives what 005-38 found, pair for pair: the 12 starts with
   another size fail with `StreamFormatException: startup error, node ...
   not found`, and the 4 with the same size read the 20,000 keys back
   ([runs/restart-head.txt](50-fix-node-size-start/runs/restart-head.txt)).
   How a start reads the meta block: `Db.startInner` calls
   `RecoverableStream.recover()`, which reads the last valid meta block
   first (since 005-40) and copies it whole into the database's own
   (`setFromOtherMetaBlock`), and only then fills out a cut meta block or
   a torn last record; `Db.handleStartParams` takes the startup distance
   from it, and `DbStarter` reruns the startup section with the builder's
   node size.
2. **A start with another size can lose the database.** `MixedNodeSize`
   ([tools/MixedNodeSize.java](50-fix-node-size-start/tools/MixedNodeSize.java)):
   20,000 keys written with size A, 100 a transaction, at a startup
   distance of 100 bytes, so that the startup section is short (136 to 178
   KB); the stream started with size B; if that succeeds, every key read
   back, 20,000 more written with B, and two restarts, with B and with A.
   On `167597a`
   ([runs/mixed-head.txt](50-fix-node-size-start/runs/mixed-head.txt),
   [runs/mixed-head-ea.txt](50-fix-node-size-start/runs/mixed-head-ea.txt)):

   | A and B | Assertions off | Assertions on (`-ea`) |
   |---|---|---|
   | B larger than A, 6 pairs | the start fails: "node ... not found" | the same |
   | B smaller, A 14 or 30, 3 pairs | the start fails: "node ... not found" | the start fails: `AssertionError: Overfull node, size=11, maxNodeSize=8` and the like |
   | B smaller, A 62, 3 pairs | the start succeeds, every key reads back, 20,000 more are written and read back; then no start opens the stream, with B or with A: `StreamFormatException: Unexpected stream pointer from KeyNode` | the start fails: "Overfull node" |
   | B equal to A, the control, 4 | starts, writes, and both restarts read all 40,000 keys | the same |

   So without assertions, as a database runs in production, a start with a
   smaller size than written can succeed and leave a database that BergDB
   cannot start again.
3. **Small databases start with any size today.** The fix's three tests of
   a start (The fix, point 6), run on `167597a` without the fix, fail
   because the start succeeds: a database just created with 8, started
   with 14; one key written with 30, its meta block's two bytes at 44
   zeroed, started with 8; one key written with 8 through the core API,
   started by the Pub API, with 30
   ([runs/tests-only.txt](50-fix-node-size-start/runs/tests-only.txt)).
   Such a database then runs with the other size.


The fix
-------

As decided (Decision):

1. **The size in the meta block.** `MetaBlock` has `maxNodeSize` at offset
   44, an unsigned short, little-endian (`getMaxNodeSize()`,
   `setMaxNodeSize()`); the reserved bytes are 46 to 126. Every meta block
   written before the fix has 0 there: a new block is zero but for its
   fields (`initBlock`), and a start copies the last valid block whole. The
   creation writes the size into the first meta block
   (`Db.writePrimordialTransaction`, beside the ID and the startup
   distance); a running database writes its own block at every meta block
   position, so every later block has the size, and so has a replica, a
   copy of the stream.
2. **No new version.** The meta block's version stays 154. The code before
   the fix, release 2026.1 among it, neither checks nor reads the reserved
   bytes (`MetaBlock.checkFormat` checks the magic bytes, the last
   transaction and the time; `RecoverableStream.readMetaBlock` the magic
   bytes and the version) and copies a block whole, so it starts a
   database of the fixed code as before, and the meta blocks it writes
   keep the size (cross X2). So release 2026.1 and the code after the fix
   can still be compared on one database, made by the fixed code. The
   Javadoc of `MetaBlock.CURRENT_VERSION` has the rule: a new field in the
   reserved bytes, which an older version can ignore, keeps the number.
3. **The check, before recovery writes.** `Db.startInner` calls
   `refuseOtherNodeSize()` just before `nodeStream.recover()`, in the same
   `try`, so that a wrong crypto key still gives `BadCryptoKey`. It reads
   the last valid meta block, as recovery does first since 005-40
   (`NodeStream.readLastValidMetaBlock()`, new, which only reads), and
   refuses a size of 0 with a `VersioningStreamException`, and another size
   than the builder's with a `StreamFormatException`. So a refused start
   writes nothing: not recovery's fill of a cut meta block or of a torn
   last record (the tests check this), nor anything of the startup. Its
   cost is a second read of that block, 6 and 128 bytes. A stream with no
   valid meta block is left to `recover()`, which refuses it as before.
4. **The messages.** Another size:

       The database's maximum node size is 8, and this start uses 30. A
       database must be started with the node size it was created with: 8,
       DbBuilder.maxNodeSize8() (the Pub API uses 30). The start has
       written nothing (bergdb 005-50).

   No size:

       The database's meta block has no maximum node size: it was written
       by a version of BergDB before 2026-10-27, which this one does not
       start (bergdb 005-50). The start has written nothing.

   Only the core API sets a node size (`DbBuilder`); the Pub API always
   uses 30. The Pub API passes the exceptions on, as
   `DatabaseBuilder.start()`'s `@throws DbException`, "If a functioning
   database could not be started", covers.
5. **Javadoc.** The four `DbBuilder.maxNodeSize*()` methods: the size must
   stay the same for a database, as it is in the stream from the creation
   and a start with another size is refused. `Db.start()`: under `@throws
   StreamFormatException`. `MetaBlock`'s format table: the field.
   `doc-files/stream-format.txt` leaves the layout to `MetaBlock`;
   unchanged.
6. **Tests**, unit tests. The first three fail without the fix (What the
   probes found, 3):
   * `DbTesterRestart.testOtherNodeSizeRefused`: every pair of 8, 14, 30
     and 62, on a database as created and on one of 300 transactions whose
     last record a crash has torn, which recovery would fill: a
     `StreamFormatException` that names both sizes, and the stream as it
     was, byte for byte; then the database's own size starts it, without
     the torn transaction.
   * `DbTesterRestart.testNoNodeSizeRefused`: a database whose meta block
     has 0, as before the fix, is refused with a
     `VersioningStreamException`, with 8 and with 30, and the stream is as
     it was.
   * `PubTester.testOtherNodeSizeRefused`: the Pub API on a database that
     the core API created with 8: the `StreamFormatException`, and the
     stream as it was.
   * `MetaBlock.Tester.maxNodeSize`: two bytes at offset 44; 0 until set;
     the bytes after it zero.
7. **`StreamDigest`** has a property, `metamask=O:N`: the digests take
   bytes O to O+N−1 of every meta block as zero. With `metamask=44:2`,
   "identical but for the bytes that hold the size" is a check.

What a start then does:

| A start of | with | gives |
|---|---|---|
| a database of the fixed code | its size | a start, as before |
| a database of the fixed code | another size | a `StreamFormatException`; nothing written |
| a database written before the fix | any size | a `VersioningStreamException`; nothing written |
| a database of the fixed code, by release 2026.1 | its size | a start; its meta blocks keep the size |


Done when
---------

A start with another node size fails with the clear error before it
writes anything (as 005-40's checks), with a test for every pair of sizes;
a stream written before the fix starts as today (dropped by the decision:
it is refused); `before-commit.sh`; StreamDigest identical on the standard
sets but for the bytes that hold the size, if any (`metamask=44:2`); the
Javadoc of the `maxNodeSize` methods says that the size must stay the same
for a database.


First step
----------

Run `RestartNodeSize` against the main tree's jar to confirm the failure,
and read how `DbStarter` and `MetaBlock` read the meta block before the
rerun, to answer question 1. Done 2026-10-27 (What the probes found, 1).


Size and order
--------------

S. Independent of the others. 005-57's prototypes change other parts of
`Db` and `DbStarter`. The later item that makes the size a property of the
stream builds on the field: a start that is given no size would take the
stream's, as it takes the startup distance (`Db.handleStartParams`).


Outcome
-------

2026-10-27, by Claude (Opus 5.5, Claude Code), as decided, at Frans's
request; in a clone on `bfa2942`. In `java/src`: `MetaBlock` (the field,
its test, the format table and the version rule), `Db` (the check, the
size at creation, the Javadoc of `start()`), `NodeStream`
(`readLastValidMetaBlock()`), the Javadoc of `DbBuilder`'s four
`maxNodeSize*()`, and the tests in `DbTesterRestart` and `PubTester`; in
`java/stress`, `StreamDigest`'s `metamask`. About 25 lines of code; the
rest is Javadoc and tests.

Checks ([runs/](50-fix-node-size-start/runs/); the probes by
[tools/run.sh](50-fix-node-size-start/tools/run.sh)):

* `before-commit.sh`: BEFORE COMMIT OK, 1,027 unit tests and 71 f-tests
  ([runs/before-commit.txt](50-fix-node-size-start/runs/before-commit.txt)).
* `level2.sh quick`: LEVEL 2 OK, as the start is level 2's
  ([runs/level2-quick.txt](50-fix-node-size-start/runs/level2-quick.txt)).
* The three new tests of a start fail without the fix, as the starts
  succeed (`tests-only.txt`).
* `RestartNodeSize`: the 12 starts with another size are refused with the
  message; the 4 others read the 20,000 keys back; the streams are as long
  as without the fix (`restart-proto.txt`).
* `MixedNodeSize`, with and without `-ea`: the 12 are refused at the
  start; the controls as before (`mixed-proto.txt`, `mixed-proto-ea.txt`).
* [tools/cross.sh](50-fix-node-size-start/tools/cross.sh)
  (`CrossNodeSize`: release 2026.1 and the fix on databases in
  directories, each step in a JVM of its own; `cross.txt`). X1, a database
  of 2026.1, 0 in its 7 meta blocks: the fix refuses it, with 30 and with
  8, with the `VersioningStreamException`, and writes nothing, as 2026.1
  then starts it as before. X2, a database of the fix, 30 in its 7 meta
  blocks: 2026.1 starts it and writes, and its new meta block has 30 too;
  then the fix refuses 8 and starts it with 30.
* `StreamDigest all`, with the fix's class, against the jars of `167597a`
  (the same `java/` as `bfa2942`) and of the fix: with `metamask=44:2`
  DIGESTS IDENTICAL (36 of 36); without it every digest differs, as every
  stream has the size in its meta blocks (`digest-*.txt`). A first run
  with the mask, beside the gates, differed in one line of 36
  (`digest-*-mask-1.txt`): `l3-node14 plain` of the jar before the fix
  had its physical cut at 1,000,000, where three runs since of each jar
  have none (0), as the fix's had; the digest from the decided cut was the
  same. The physical cut waits for durability, so its timing may differ
  (`StreamDigest`'s Javadoc).

Every database written before the fix is refused by the code after it
(Frans: "There are none."). Among them the bench databases of 007-05
(`~/fl/bench/007-05/data`, made at `851acdf`, and s1's): a measurement of
a build after the fix makes them again, about 1.5 minutes each at 10M keys
on F53 (the 005-57 session notes it in 005-57).
