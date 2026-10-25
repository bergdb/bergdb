005-39. Fix: getPosOfTransCompletedBefore, a wrong Javadoc and a cut stream
==========================================================================

Status: done (2026-10-25). Kind: fix. Created 2026-10-25.

Found on 2026-10-25 by Claude (Opus 5.5, Claude Code), at Frans's request
("Investigate RecoverableStream.java:516. The TODO there. Is this a bug?
Or bad doc or just a bad comment."), with a probe on `425d7a7`, in
[39-fix-trans-completed-before/](39-fix-trans-completed-before/). Added
and fixed at his request ("Yes", to "Should I register this as a 005 Fix
entry and do it?").


The issue
---------

Under the Javadoc of `RecoverableStream.getPosOfTransCompletedBefore(spos)`
was a TODO: "This doc is not true, or we have a bug. This method does not
iterate to find last valid transaction, just any recent transaction
completely written before stream position 'spos'." Both: the Javadoc was
wrong, and in a stream whose front is cut, so was the method.

**The Javadoc** said: "Returns the last valid transaction that was
completely written before stream position 'spos'. If there is no such
transaction, the spos of the very first valid transaction is returned
instead." The method returns the transaction named by the last valid meta
block at or before `spos`: the last one completed before that meta block
was written (`NodeStream.appendNodes` names each transaction after its
append). It was completed before `spos`, but the transactions written
between the meta block and `spos`, up to 200,000 bytes, come after it. If
the meta block names none, it returns the first transaction, at 128, also
when that one is not committed.

The probe (`CompletedBeforeProbe`, [probe-before.txt](39-fix-trans-completed-before/probe-before.txt)),
part A: 1,300 committed transactions of 1000 bytes, each named as
`appendNodes` does. At 1,305 positions, every 997 bytes, the result was
the last transaction completed before the position at 4 of them, with up
to 200 completed between the two; at 399,000 it was 198,128, and the last
one completed before 399,000 is at 397,256. Part B: when the first
transaction failed, the result is 128, that one, not 1128, the committed
one after it.

**A cut stream.** After `pretruncate`, the meta blocks before the first
position are not searched (since 2026-10-13). For an `spos` before the
first meta block at or after the first position, there was none, and the
method threw `NullPointerException`. That meta block names the last
transaction completed before it, which can start before the cut; then an
`spos` from there up to a meta block that names a transaction after the
cut gave a position that cannot be read. `MemoryStream` and
`FileStream` cut whole 1 MB arrays and whole files, whose sizes are
multiples of 200,000 bytes, so their first position is normally a meta
block's, and that meta block names a transaction before it.

| Part | Stream | Call | Result |
|---|---|---|---|
| C | A, cut at 1,000,000 (`MemoryStream`) | `spos` 0, 500 | `NullPointerException` |
| C | | `spos` 1,000,000 to 1,199,999 | 998,640; a read there: `StreamIoException`, "Cannot read from position 998640, first valid position is 1000000." |
| C | | `spos` 1,200,000, 1,250,000 | 1,198,768, which can be read |
| D | a database cut by reclaim at 372,720 (`CutStream`, as in `Reclaim.Tester`) | `createTransIterator(0)`, `(372720)`, `(372721)`; `print(out, 0)` | `NullPointerException` |
| D | | `createTransIterator(401000)` | from 398,128 to the end |

Who calls it: the iterators that do not start at an exact position,
`NodeStream.createTransIterator` (from `NodeStream.print`, the tests in
`NodeStreamTester` and the dev tool `IsDeterministic`), and
`RecoverableStream.Iterator` (its own tests); all from 0. Startup does not:
since 2026-10-13, `Db.getStartupPosFromLastTransaction` reads from the
exact position that the last valid meta block names
(`createTransIteratorFromExactStartupPos`). So BergDB itself never met
either fault; from 0, in a stream that is not cut, the result, 128, is
right. A test or a tool that iterated over or printed a database that
reclaim had cut would have.


The fix, proposed
-----------------

* The Javadoc says what the method does: the transaction named by the
  last valid meta block at or before `spos`, a place to read on from, in
  general not the last one completed before `spos`; the first
  transaction, committed or not, if the meta block names none. The same
  in the Javadoc of `RecoverableStream.Iterator` and of
  `NodeStream.createTransIterator`. The TODO goes.
* The method gives the same as before in a stream that is not cut. In a
  cut stream, when there is no meta block at or before `spos`, or the one
  there names a transaction before the first position, it takes the meta
  blocks after it, up to the end of the stream, until a valid one names a
  transaction at or after the first position. That one can come after
  `spos`, and the transactions between the first position and it are not
  found: the stream holds no other way to find where a transaction starts
  there. If there is none, it throws a `StreamFormatException`. That does
  not happen in a database's stream: reclaim cuts at or before the
  transaction that the last valid meta block names
  (`Reclaim.pretruncateIfPossible`, `metaTransPos >= row.pCut`), which
  recovery needs too.

Not chosen: to do what the old Javadoc said, a search from the meta
block's transaction for the last committed one completed before `spos`.
No caller needs it: each reads on from the result to the end of the
stream, and skips a transaction that is not committed. Nor to refuse a cut
stream with a clear exception, which would leave the iterators and
`print()` of no use on a database that reclaim has cut.


Done when
---------

* Unit tests. A stream that is not cut: the result at every 997 bytes is
  the transaction named by the last meta block at or before the position.
  A `MemoryStream` cut at 1,000,000: the positions of part C give the
  transaction the meta block at 1,200,000 names, and the iterator from 0
  reaches the end; a stream cut after the transaction its last meta block
  names gives the `StreamFormatException`. A database cut by reclaim on a
  `CutStream`: `createTransIterator` from 0, from the cut and from one
  byte after it start at the same transaction after the cut and reach the
  end of the stream, and so does `print(out, 0)`. The tests with a cut
  fail without the fix.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Size and order
--------------

S, any time: one method, the Javadoc of two iterators, tests. Nothing
that writes the stream or starts a database calls the method, so the
streams do not change.


Outcome
-------

2026-10-25, by Claude (Opus 5.5, Claude Code), as proposed.

* `RecoverableStream.getPosOfTransCompletedBefore` has the new Javadoc,
  and a dated comment in place of the TODO. Where the old code read one
  meta block, it reads that one and, while it names a transaction before
  the first position, the next ones, up to the end of the stream; when
  there is no meta block at or before `spos`, it starts at the first one
  at or after the first position. It returns as before in a stream that
  is not cut. When no valid meta block names a transaction at or after
  the first position, it throws `StreamFormatException`: "No valid meta
  block names a transaction at or after the first position of the
  stream, P."
* The Javadoc of `RecoverableStream.Iterator` and of
  `NodeStream.createTransIterator` says where they start.

Tests:

* `RecoverableStream.Tester.testPosOfTransCompletedBefore`: part A's
  stream; at every 997 bytes, the result is the transaction named by the
  last meta block at or before the position (or 128, at the first), and
  at 399,000 it is 198,128. Passes before the fix too: it states what the
  method did.
* `RecoverableStream.Tester.testPosOfTransCompletedBeforeAfterCut`: the
  stream cut at 1,000,000; at 0, 500, 1,000,000, 1,050,000 and 1,199,999
  the result is the transaction that the meta block at 1,200,000 names,
  after the cut; `RecoverableStream.Iterator` from 0 gives every
  transaction from it to the end; a stream of 1,100 transactions cut at
  1,000,000, after the transaction its last meta block names, throws
  `StreamFormatException`, at 0 and at 1,050,000. Without the fix:
  `NullPointerException`.
* `Reclaim.Tester.testTransIteratorAfterCut`: a database on a `CutStream`,
  run as in `testRestartAfterCut` until reclaim cuts it;
  `NodeStream.createTransIterator` from 0, from the cut and from one byte
  after it each start at the same transaction, at or after the cut, and
  reach the end of the stream, through the last transaction; `print(out,
  0)` starts there too. Without the fix: `NullPointerException`. 47 ms.

The probe with the fix
([probe-after.txt](39-fix-trans-completed-before/probe-after.txt)): parts A
and B as before; in part C every position gives 1,198,768, which can be
read; in part D, the iterators from 0, from the cut, from one byte after
it and from 401,000 go from 398,128, the transaction that the meta block
at 400,000 names, to the end of the stream, and `print(out, 0)` passes.
The transactions from the cut, 372,720, to 398,128 are not found.

`before-commit.sh`: BEFORE COMMIT OK (1010 unit tests, 67 f-tests).
