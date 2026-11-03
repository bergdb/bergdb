005-82. Fix: parsing corrupt transaction data must fail the database
==================================================================

Status: open; planned for release 2026.2, the live-read part only
(Frans, 2026-11-03, 15:27, 016-01's Q1: "as recommended"; see Plan for
2026.2). Kind: fix. Created 2026-11-02.

Split from 005-74 when Frans selected its option A, the size checks.
Found in 012-14, section 6.7; the finding and its probe remain there.


The issue
---------

`Db.getTrans` catches storage and format errors from `TransIterator.next`,
but calls `getStoredTrans` outside that `try`. A node checksum failure in
the latter escapes as `StreamChecksumException` and leaves the database
active. A parser bounds exception can escape too. This contradicts the
read-failure contract of levels.md, section 3, and 005-34.

005-74's option A checks sizes before allocations and bounds parsing by
the declared record. It does not move the parse into the failure handler.
The C API already fails the database on a parsing error (012-03).


Proposed fix
------------

Parse inside `getTrans`'s storage-failure handling. Refuse malformed
records with a format error, retaining its cause when the database fails.
Keep invalid caller positions and expired reads as their existing errors.


Done when
---------

Regressions corrupt a node checksum in an otherwise readable transaction
and exercise a malformed record. Each read fails the database; later reads
and writes are refused with the first failure as cause. Valid, expired and
invalid-position cases retain their behavior. `before-commit.sh` passes.


Plan for 2026.2
---------------

Written 2026-11-03 for 016-05 (W4). Frans's answer to 016-01's Q1 (15:27):
"Q1: as recommended": the live read only. `getTrans` fails the database on
a corrupt record, as every other read does, and keeps the cause. How
startup handles damaged tails stays with 014-01: `Db.readTransactions`, the
take and recovery are not changed. With D7 (016-01, section 10): Java only.

The steps, by agent F1 (016-05), in `/Users/f/fl/bench/016/005-82/repo`:

1. **The clone** (0.05 hours): `git clone -q /Users/f/fl/repos/bergdb
   /Users/f/fl/bench/016/005-82/repo`; its HEAD into
   `/Users/f/fl/bench/016/005-82/BASE`.
2. **The fix** (0.25 hours), `java/src/bergdb/core/Db.java`, `getTrans`:
   * `ti.getStoredTrans()` (`StoredTrans.parse`) moves into the `try`
     around `ti.next()`. Its `StreamFormatException`, with the subclasses
     `StreamChecksumException` and `VersioningStreamException`, goes to
     `failOnStorage(e, "A read")` as `next()`'s does: the database fails,
     with the exception as the cause.
   * The end of the stream (`next()` false) stays outside the `try`, an
     `IllegalArgumentException` that fails nothing, as since 005-43. The
     position checks before the read and the expiry by a cut
     (`isReadBelowCut`, only `next()` reads the stream) stay as they are.
   * Read `StoredTrans.Parser` and the node parsers it calls: can a
     malformed record still give an unchecked exception other than a
     `StreamFormatException` (an index out of bounds, a negative array
     size), after 005-74's checks? If one can, `getTrans` wraps it at the
     parse in a `StreamFormatException` ("a malformed record at TPOS",
     the exception as its cause) and fails the database with it (P7: a
     database with corrupt data or a bug does not run on). If the same
     exception can reach another read (a load of the Dag), that is a
     finding for the coordinator, not fixed here.
3. **The Javadoc** (0.1 hours): `getTrans`'s `@throws DbFailedException`
   adds "or its record is corrupt: a node's checksum fails, or the record
   is malformed (bergdb 005-82)"; `Connection.transactionInfo()`'s
   `DbFailedException` line checked against it.
4. **The tests** (0.35 hours), `java/src/bergdb/core/DbTesterFailure.java`:
   * `FaultStream` gets `volatile long flipAt = -1`: a read that covers
     that stream position gets its byte flipped (XOR 0x01) in the
     caller's buffer. The record's size and last byte stay right, so
     `next()` passes and the parse fails.
   * `testGetTransChecksum` (unit): two transactions, synced; `flipAt` at
     a byte inside a node of the first one's record, chosen so that the
     node's checksum fails. `getTrans` of it throws `DbFailedException`
     whose cause is a `StreamChecksumException`; then `assertRefused` (the
     helper of `testGetTrans`): later reads and writes are refused with
     that cause; `getTrans` of the second transaction too.
   * `testGetTransMalformed` (unit): as the first, with the flipped byte
     in a node's size, so that the parse refuses the record (005-74's "a
     node must fit inside its declared record"); the cause is a
     `StreamFormatException`.
   * Each fails on `main` before the fix: the exception escapes as it is
     and the database stays active (as 012-14, section 6.7's probe). The
     agent records the mutation (the fix reverted) and its two failures in
     the Log.
   * `testGetTrans`, `testGetTransBelowTheCut` and the tests of invalid
     positions (`DbTester`, 005-34 and 005-43) pass unchanged: valid,
     expired and invalid-position reads keep their behaviour.
5. **The gate**: `java/before-commit.sh`, `BEFORE COMMIT OK` (about 2
   minutes). If it fits: `java/stress/level1.sh quick` (75 s), whose unit
   tests include the read-failure tests.
6. **The review** (016-05, section 5): 0.5 hours of another agent; its
   findings answered here, in the Log (0.15 hours).
7. **The hand-off** (016-05, section 4): this entry's Log and an Outcome
   in the clone, Status "done" for the commit; the coordinator commits and
   sets 005's table. A line for `releases/next.md` (016-03): "a corrupt
   transaction record read by `Connection.transactionInfo()` fails the
   database (005-82)".

Size: about 1.5 agent-hours, the review's included. Depends on nothing;
first in F1's row. No stop for Frans: Q1 decided the scope. The C clone
fails the database here already (012-03); after the fix both agree
(012-14, section 6.7), and nothing changes in C.

**State** (2026-11-03): planned, not started. No clone yet. The code was
read at `df6ad50`: `Db.getTrans` (lines 1455 to 1496), `failOnStorage`,
`NodeStream.TransIterator`, `StoredTrans.parse`, and
`DbTesterFailure.testGetTrans` and `FaultStream`. To resume: step 1, or
the step after the last one in the Log.


Log
---

2026-11-02. Split from 005-74 during its option A implementation. The
checksum finding remains open; no production change for it in 005-74.

2026-11-02. Frans asked to distinguish expected incomplete crash tails
from unexpected corruption before implementing this change. 005-83,
"Power-loss tail experiment", now supplies the evidence: the `lazy`
case opens with damaged unforced data before an intact later meta block.
An ordinary read fails the instance; `getTrans` reports the parsing
error, stays active and accepts another write. Its section 4 recommends
deciding the startup recovery contract first. Making live-read error
handling consistent would not by itself make the damaged tail recover.
This item remains open; its implementation and that policy decision have
not been carried out.

2026-11-03. Planned for release 2026.2 (016-05), the live-read part only,
by Frans's answer to Q1; "Plan for 2026.2" above. Nothing changed yet.
