005-82. Fix: parsing corrupt transaction data must fail the database
==================================================================

Status: done (2026.2), the live-read part only (Frans, 2026-11-03, 15:27,
016-01's Q1: "as recommended"; see Plan for 2026.2 and Outcome); startup's
handling of damaged tails stays with 014-01. Kind: fix. Created
2026-11-02. Closed 2026-11-03.

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

**State** (2026-11-03, 16:19, F1): done; the final hand-off is
`/Users/f/fl/bench/016/005-82/handoff/` (with `review.txt`), for the
coordinator's combined gate and commit.


Outcome
-------

2026-11-03, by F1 (016-05), in `/Users/f/fl/bench/016/005-82/repo` from
`main` at `47ba87f`:

* `Db.getTrans` parses the record inside its failure handling (a new
  `Db.parseTrans`): a node's checksum or a malformed record fails the
  database, with the exception as the cause, as every other read does
  (docs/levels.md, section 3; 005-34). Any other `RuntimeException` of the
  parse (a node with a right checksum whose fields do not fit its size)
  becomes the cause of a `StreamFormatException`, which fails the database
  too (010-01, P7); an `Error` is thrown as it is. Valid, expired and
  invalid-position reads are as they were. `Db.readTransactions`, the take
  and recovery are not changed (014-01).
* `getTrans`'s Javadoc names the corrupt record; `Connection.transactionInfo()`
  and docs/levels.md were right already.
* Tests (unit, `DbTesterFailure`, with `FaultStream`'s new `patchAt` and
  `patch`): `testGetTransChecksum`, `testGetTransMalformed`,
  `testGetTransUncheckedParseError`. All three fail with the fix reverted;
  the third alone without `parseTrans`'s wrap.
* `before-commit.sh`: `BEFORE COMMIT OK (82 s)`, and after the review's
  nit `BEFORE COMMIT OK (108 s)`. Reviewed by the coordinator: no faults;
  its nit taken.
* The finding of the same unchecked exceptions in the Dag's loads is
  015-07.
* For `releases/next.md`: "a corrupt transaction record read by
  `Connection.transactionInfo()` fails the database (005-82)".

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

2026-11-03, 15:58 to 16:12, by F1 (016-05), in
`/Users/f/fl/bench/016/005-82/repo` from `main` at `47ba87f`, steps 1 to 4:

* **The fix**, `Db.getTrans`: the parse (`ti.getStoredTrans()`) moved into
  the `try` around `ti.next()`, through a new `Db.parseTrans`. Its
  `StreamFormatException`, with `StreamChecksumException` and
  `VersioningStreamException`, goes to `failOnStorage(e, "A read")` as
  `next()`'s does: the database fails with it as the cause. The end of the
  stream, the position checks and the expiry by a cut are as they were;
  only `next()` reads the stream.
* **Step 2's question**: yes, an unchecked exception other than a
  `StreamFormatException` can still come. The node parsers check the
  node's checksum first, but not every field against the node's size:
  `StoredKeyNode.parse` the key count (up to 32,767), `StoredValueNode.parse`
  the value's size (negative: `NegativeArraySizeException`; too large:
  `ArrayIndexOutOfBoundsException`) and the key's size,
  `StoredTopNode.parse` the pointer count (only an `assert`). A node with a
  right checksum and such a field (a writer's bug, or one random damage in
  65,536, Fletcher-16) throws one. So `parseTrans` makes any
  `RuntimeException` other than a `StreamFormatException` the cause of a
  `StreamFormatException` ("A malformed record at stream pos ..."), which
  fails the database (010-01, P7). An `Error` (that `assert` with `-ea`, an
  `OutOfMemoryError`) is thrown as it is and fails nothing, as in the other
  reads.
* **Finding for the coordinator** (not fixed here): the same exceptions
  reach the Dag's loads (`NodeStream.readNode`, `bytesToNode`), and there
  they escape. `Db.getOneInternal`, `Db.getMany` and the reads before a
  transaction's go point catch only `StreamException`. A probe (outside
  the repository, on the clone's jar) gave every key node read a key count
  of 32,767 with the checksum made right: `getOne`, `getMany`
  (`DbUtil.checksum`) and a put each threw
  `ArrayIndexOutOfBoundsException: Index 1024 out of bounds for length
  1024`, and a later put was taken: the database stayed active, against
  docs/levels.md, section 3, and P7. After the go point `fail()` catches
  every `Throwable`, so a load there fails the database.
* **The Javadoc**: `getTrans`'s `@throws DbFailedException` names the
  corrupt record (a node's checksum fails, or the record is malformed;
  005-82) and the cause. `Connection.transactionInfo()`'s line ("If the
  database has failed, before or in this read") is right as it is, and
  docs/levels.md, section 3, lists `getTrans` among the reads that corrupt
  data fails already: both unchanged.
* **The tests**, `DbTesterFailure`. `FaultStream` got `patchAt` and `patch`
  in place of the plan's `flipAt`: a read that covers those stream
  positions gets those bytes in the caller's buffer, so that a test can
  also give a node whose checksum is right. Three unit tests, on the value
  node of /a in the first of two synced transactions:
  `testGetTransChecksum` (a byte of the value flipped:
  `StreamChecksumException`), `testGetTransMalformed` (the high byte of
  the node's size flipped: the parse's `StreamFormatException`, "Bad node
  size") and `testGetTransUncheckedParseError` (the value's size -1, the
  checksum made right: a `StreamFormatException` whose cause is a
  `NegativeArraySizeException`). In each, `getTrans` of the first fails the
  database with that cause; `assertRefused`; `getTrans` of the second is
  refused with the same cause; nothing is appended; a restart on a copy
  reads both values and both transactions.
* **Mutations**, `unit.sh -c DbTesterFailure -m testGetTrans`: (1) the fix
  reverted (`Db.java` of `47ba87f`): the three tests fail, each with "the
  read did not fail the database:" and the `StreamChecksumException`, the
  `StreamFormatException` "Bad node size, 16777256, at offset 32 of
  transaction at 264, size 120." and the `NegativeArraySizeException: -1`
  escaping; `databasesStopped` names the three. (2) The parse in the `try`
  without `parseTrans`'s wrap: only `testGetTransUncheckedParseError`
  fails. With the fix the five pass, `testGetTrans` and
  `testGetTransBelowTheCut` unchanged.
* **The gate** (step 5): `java/before-commit.sh`, 16:10 to 16:11: `BEFORE
  COMMIT OK (82 s)`, 1,096 unit tests and 78 f-tests. `level1.sh quick`
  not run: other agents' gates and level scripts kept F53 busy (one at a
  time).

2026-11-03. Reviewed 2026-11-03 by the coordinator (H5, 016-05, section
5): no faults. The fix is within Q1's scope; `parseTrans` wraps only a
`RuntimeException` (an `Error` passes); the three tests and the two
mutations are right; the restart check shows that the damage was in the
reads only. One nit, optional: `FaultStream`'s class Javadoc sat above
`storageThreads()`'s comment, not above the class (so before this
change). Answer: taken, the comment moved above `static class
FaultStream`; `before-commit.sh` again, 16:18 to 16:20: `BEFORE COMMIT OK
(108 s)`, 1,096 unit tests and 78 f-tests. The finding of 16:12 (the Dag's
loads) is registered as 015-07. Closed: Outcome and Status above.
