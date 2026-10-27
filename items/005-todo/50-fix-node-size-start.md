005-50. Fix the start with another node size
=============================================

Status: open; fix proposed 2026-10-27. Kind: fix. Created 2026-10-26.

Found in 005-38 ([report](38-writes-at-scale/report.md), section 6), by a
subagent (Claude, Opus 5.5) measuring node sizes; registered at Frans's
request (2026-10-26: "Yes to node-size fix entry. For now, it should fail
with a good error message. This should be the scope. Other options are
interesting, but later and in some other item.").

The fix proposed on 2026-10-27 by Claude (Opus 5.5, Claude Code), at
Frans's request ("Propose a solution were the node size is stored in the
MetaBlock."): the size in four of the meta block's reserved bytes, checked
before recovery writes (The fix, proposed). The prototype, the probes and
their runs are in [50-fix-node-size-start/](50-fix-node-size-start/). No
change to `java/`.


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

   Proposed: in the meta block, at offset 44, an int (4 bytes,
   little-endian, as the startup distance at 40). It needs no new version:
   the code before the fix neither checks nor reads the reserved bytes and
   passes them on, and the fixed code reads 0 in a block written before it
   (The fix, proposed, points 1 and 2). A record could hold it in the three
   unused bytes of its header, also without a new format; but a start
   reaches a record only in recovery, which writes, or after it, and the
   size would be repeated in every record. The meta block is what a start
   reads first, and it holds the database's other constants, its ID and
   its startup distance.
2. The error's type: a new exception, or `DbException` with a message;
   what the Pub API (`DatabaseBuilder`) shows.

   Proposed: `DbException` with a message, no class of its own (The fix,
   proposed, point 5). The Pub API shows the same exception:
   `DatabaseBuilder.start()` passes it on, under its `@throws
   DbException`.
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
   a start (The fix, proposed, point 7), run on `167597a` without the fix,
   fail because the start succeeds: a database just created with 8,
   started with 14; two keys written with 14 (one value of 200 KB),
   started with 30; one key written with 8 through the core API, started
   by the Pub API, with 30
   ([runs/tests-only.txt](50-fix-node-size-start/runs/tests-only.txt)).
   Such a database then runs with the other size.


The fix, proposed
-----------------

1. **The size in the meta block.** `MetaBlock` gets `maxNodeSize` at
   offset 44, an int of 4 bytes, little-endian (`getMaxNodeSize()`,
   `setMaxNodeSize()`); the reserved bytes become 48 to 126. 0 means not
   recorded, and every meta block written before the fix has 0 there: a
   new block is zero but for its fields (`initBlock`), and a start copies
   the last valid block whole. The creation writes the size into the first
   meta block (`Db.writePrimordialTransaction`, beside the ID and the
   startup distance); a running database writes its own block at every
   meta block position, so every later block has the size too, and so does
   a replica, a copy of the stream. One exception to the zeros: a meta
   block that a start with a wrong crypto key filled out after a crash,
   before 005-40's fix of 2026-10-25, and that came out valid (1 time in
   256, 005-40) has garbage from the cut on, so perhaps in bytes 44 to 47,
   and a start would be refused with a garbage size. Only a database
   written between 2026-10-15 (today's record format) and 2026-10-25 can
   have one; none is known.
2. **No new version.** The meta block's version stays 154. The code before
   the fix, release 2026.1 among it, neither checks nor reads the reserved
   bytes (`MetaBlock.checkFormat` checks the magic bytes, the last
   transaction and the time; `RecoverableStream.readMetaBlock` the magic
   bytes and the version) and copies a block whole, so it starts a
   database of the fixed code as before, and the meta blocks it writes
   keep the size (the prototype, cross X2). A new version would, by
   005-40's rule (new databases only), refuse today's databases, against
   "a stream written before the fix starts as today", or need two versions
   read; and release 2026.1 could not start a database of the fixed code,
   while the comparisons of versions start one database with several jars
   (005-57's `f53-57.sh`). The Javadoc of `MetaBlock.CURRENT_VERSION` gets
   the rule: a new field in the reserved bytes, whose 0 means "not
   recorded", keeps the number.
3. **The check, before recovery writes.** `Db.startInner` calls
   `refuseOtherNodeSize()` just before `nodeStream.recover()`, in the same
   `try`, so that a wrong crypto key still gives `BadCryptoKey`. It reads
   the last valid meta block, as recovery does first since 005-40
   (`NodeStream.readLastValidMetaBlock()`, new, which only reads), and
   throws if the block's size is neither 0 nor the builder's. So a refused
   start writes nothing: not recovery's fill of a cut meta block or of a
   torn last record (the tests check this), nor anything of the startup.
   Its cost is a second read of that block, 6 and 128 bytes. A stream with
   no valid meta block is left to `recover()`, which refuses it as before.
4. **A stream written before the fix** has 0 in its meta blocks and starts
   as today, unchecked: with its own size it starts; with another it fails
   as today, or starts (question 3). After recovery the start puts the size
   it runs with in the database's meta block, so that the meta blocks it
   writes have it, and the stream is checked from the first of them on,
   after at most 200 KB of writes (the prototype, cross X1). That is the
   size the database runs with from then on, so the only one that a later
   start can succeed with. Not proposed: the size only at creation, one
   line less, which leaves today's databases unchecked for good.
5. **The error (question 2): a `DbException`**, with the message

       The database's maximum node size is 8, and this start uses 30. A
       database must be started with the node size it was created with: 8,
       DbBuilder.maxNodeSize8() (the Pub API uses 30). The start has
       written nothing (bergdb 005-50).

   No class of its own: only the core API sets a node size (`DbBuilder`);
   the Pub API always uses 30 and has no setting for it. So no program
   needs to tell this failure from others, and the person who reads the
   message learns what to do. A class would be API for a case that the
   later item may remove (the size from the stream, which the builder then
   need not set). The Pub API passes the exception on, as
   `DatabaseBuilder.start()`'s `@throws DbException`, "If a functioning
   database could not be started", covers; a Pub API user meets it only
   with a database that the core API created with another size than 30.
6. **Javadoc.** The four `DbBuilder.maxNodeSize*()` methods: the size must
   stay the same for a database, as it is in the stream from the creation
   and a start with another size is refused. `Db.start()`: `@throws
   DbException`. `MetaBlock`'s format table: the field.
   `doc-files/stream-format.txt` leaves the layout to `MetaBlock`;
   unchanged.
7. **Tests**, unit tests. The first three fail without the fix (What the
   probes found, 3):
   * `DbTesterRestart.testOtherNodeSizeRefused`: every pair of 8, 14, 30
     and 62, on a database as created and on one of 300 transactions whose
     last record a crash has torn, which recovery would fill: a
     `DbException` that names both sizes, and the stream as it was, byte
     for byte; then the database's own size starts it, without the torn
     transaction.
   * `DbTesterRestart.testNodeSizeOfOldStream`: a stream whose meta block
     has 0, as before the fix, starts unchecked with its size; after a
     transaction that takes it past a meta block, a start with another
     size is refused, and one with its size reads the data.
   * `PubTester.testOtherNodeSizeRefused`: the Pub API on a database that
     the core API created with 8: the `DbException`, and the stream as it
     was.
   * `MetaBlock.Tester.maxNodeSize`: offset 44; 0 until set; the reserved
     bytes after it zero.
8. **`StreamDigest`** gets a property, `metamask=O:N`: the digests take
   bytes O to O+N−1 of every meta block as zero. With `metamask=44:4`,
   "identical but for the bytes that hold the size" is a check.

What a start then does:

| A start of | with | gives |
|---|---|---|
| a database created by the fixed code | its size | a start, as today |
| a database created by the fixed code | another size | the `DbException`; nothing written |
| a database written before the fix | its size | a start, as today; its next meta block gets the size |
| a database written before the fix | another size | as today: a failure, or a start (question 3) |
| a database written before the fix, with the size in its last meta block | another size | the `DbException`; nothing written |
| a database of the fixed code, by release 2026.1 | its size | a start; its meta blocks keep the size |


The prototype
-------------

[prototype.diff](50-fix-node-size-start/prototype.diff), on `167597a`
(`6260106` has the same `java/`): seven files, 271 lines added. About 25
of them are code: the check and the size after recovery in `Db`, the field
in `MetaBlock`, a method in `NodeStream`; the rest is Javadoc and tests
(140 lines in `DbTesterRestart` and `PubTester`), and 32 lines in
`StreamDigest`. The checks, in a clone
([runs/](50-fix-node-size-start/runs/), by
[tools/run.sh](50-fix-node-size-start/tools/run.sh), about 4 minutes on
F53, and `before-commit.sh`):

* `before-commit.sh`: BEFORE COMMIT OK, 1,027 unit tests and 71 f-tests
  ([runs/before-commit.txt](50-fix-node-size-start/runs/before-commit.txt)).
* `RestartNodeSize`: the 12 starts with another size are refused with the
  message; the 4 others read the 20,000 keys back; the streams are as long
  as without the fix (`restart-proto.txt`).
* `MixedNodeSize`, with and without `-ea`: the 12 are refused at the
  start; the controls as before (`mixed-proto.txt`, `mixed-proto-ea.txt`).
* [tools/cross.sh](50-fix-node-size-start/tools/cross.sh) (`CrossNodeSize`:
  release 2026.1 and the prototype on databases in directories, each step
  in a JVM of its own; `cross.txt`). X1, a database of 2026.1, 0 in its 7
  meta blocks: the prototype starts it with 30, and with 8 fails as today;
  after the prototype has written 200 KB more, the new meta block has 30,
  the prototype refuses 8 and 62, and 2026.1 still starts it. X2, a
  database of the prototype, 30 in its 7 meta blocks: 2026.1 starts it
  and writes, and its new meta block has 30 too; then the prototype
  refuses 8 and starts it with 30.
* `StreamDigest all`, the prototype's class against the jars of `167597a`
  and of the prototype: with `metamask=44:4` DIGESTS IDENTICAL (36 of 36);
  without it every digest differs, as every stream has the size in its
  meta blocks (`digest-*.txt`).


Done when
---------

A start with another node size fails with the clear error before it
writes anything (as 005-40's checks), with a test for every pair of sizes;
a stream written before the fix starts as today; `before-commit.sh`;
StreamDigest identical on the standard sets but for the bytes that hold
the size, if any (with the fix as proposed: `metamask=44:4`); the Javadoc
of the `maxNodeSize` methods says that the size must stay the same for a
database. With the fix as proposed, also: release 2026.1 starts a database
of the fixed code (`tools/cross.sh`).


First step
----------

Run `RestartNodeSize` against the main tree's jar to confirm the failure,
and read how `DbStarter` and `MetaBlock` read the meta block before the
rerun, to answer question 1. Done 2026-10-27 (What the probes found, 1).


Size and order
--------------

S. Independent of the others. With the prototype, the fix is to apply
`prototype.diff` and run `before-commit.sh` and `tools/run.sh`. 005-57's
prototypes (not applied) change other parts of `Db` (from line 1077) and
`DbStarter`, so no overlap. The later item that makes the size a property
of the stream builds on the field: a start that is given no size would
take the stream's, as it takes the startup distance
(`Db.handleStartParams`).
