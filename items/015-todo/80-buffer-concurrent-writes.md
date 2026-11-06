015-80. Fix: the buffer issues concurrent writes to a single-writer underlying stream
=====================================================================================

Status: done 2026-11-06, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R5's finding R5-F5 (items/016-release-2026-2/06-reviews/R5.md,
section R5-F5: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R5/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


The argument (night 006-12, 2026-11-05)
---------------------------------------

Frans, 2026-11-05, 21:46, to the coordinator: "Yes. I also lean towards
option 2. So option 2 unless the agent strongly suggests something else.
The agent can choose, dont wait for me." The options: (1) queue every
physical cut to the buffer's thread; (2) one separate lock that
serializes every non-read call to the stream below, not the buffer's
monitor; (3) change AppendOnlyStream's contract.

### Chosen: option 2, with getFirstPos() from a kept value

`BufferedStream` gets `ioLock`, a fair `ReentrantLock`. Every call that
`BufferedStream` makes to the stream below, but read() and the
constructor's, is made holding it, and nothing else is done holding it:

* the thread's appends in `flushToStream`, each `stream.append` on its
  own (a flush that wraps the ring makes two);
* `pretruncate`: the writer's cut at or below the flushed length, and
  the thread's pending cut in `flushToStream`, each followed, under the
  same hold, by `stream.getFirstPos()`, kept in a volatile field;
* `close`, in `closeStream()`, by the thread as it ends and by `close()`.

`getFirstPos()` returns the kept value and does not call the stream
below. It is on every commit's path (`NodeCollection.resolvePointers`
asks it for each stream pointer without a handle of each index node
written), so under the lock a commit would wait for the thread's append
and its force, again and again. The kept value is exact: a stream's first
position changes only at a cut (AppendOnlyStream; FileStream,
MemoryStream, CutStream, SalsaStream and OneFileStream set it, or pass
the cut on, in pretruncate itself), every cut of the stream below is made
by `BufferedStream` (it owns the stream; nothing else cuts it), and the
value is read right after each cut, before the cut's caller goes on. The
constructor reads it first, as it reads the length, before the thread
starts. Harness 6.3's check "getFirstPos() during a flush" then sees no
call at all.

### Why not the others

* Option 1 makes the cut asynchronous to the writer, and the writer
  depends on its own cut being made: `resolvePointers` skips a stream
  pointer below `getFirstPos()` and reads the header of any other
  (Reclaim.Tester.testWritesAfterCut). With the cut left to the thread,
  `getFirstPos()` is the old position until the thread makes it, and a
  header read that the check let through can meet the cut:
  `ReadBelowFirstPosException` in a commit. Today Reclaim's cut is made
  at once (it cuts behind the durable length, so it is never a pending
  cut, 015-82), and the writer never races a cut. Option 1 would also
  need a cut's failure published as a flush's, and a wake of an idle
  thread. A mix, `tryLock` and the thread's pending cut when the lock is
  busy, brings the same race back for that cut: not taken.
* Option 3 moves the burden to every stream below (FileStream, the test
  streams, a user's own), each with an argument of its own; FileStream's
  own locks happen to cover it today (R5), but the contract would no
  longer say so. Frans leans to 2.

### The cost: a cut can wait for one append

A cut that arrives while the thread appends waits for that append and,
with FileStream's default, its force. The only cut on a commit's path is
Reclaim's (`cutIfDurable`, in `transactionCompleted`, under the
database's write lock), once per reclaim cut. It waits for at most one
`stream.append`: the lock is fair, so the waiting cut is next when the
append ends, and each append of a flush takes the lock alone. An append
is at most half the buffer (5 MB by default) and its force: on F53 an
append of 2.5 MB with its force took 17 ms on average and 144 ms at the
longest (005-46, out/stream-wait.txt); on s1 a force can take seconds.
The other writers wait with it (it holds the write lock); readers do
not. This is a wait for the device, as a writer's wait for room in the
buffer is (P1, 005-46, decision 5), not work of BergDB's for the whole
database. Before the fix the cut did not wait: it ran beside the append,
which is the fault. For a reviewer: the one new wait on a commit's path.

### Locks and their order

W, the database's write lock (held by every caller of `BufferedStream`
but read(), as the contract says; `StorageManager.handleStreamException`
also closes from a reader or the thread, see below); B, the buffer's
monitor; I, `ioLock`; D, `StorageManager`'s `d1Lock`; S, the stream
below's own locks.

* B and I are never nested, in either order: `pretruncate` leaves B
  before it takes I; `flushToStream` takes I only around `stream.append`
  and `stream.pretruncate` (with `getFirstPos`), and B only between them;
  `closeStream` takes B, for `closeFailure`, after it leaves I.
* Holding I, a thread calls only the stream below (S, leaves: a stream
  below has no reference to the layers above) and writes a volatile.
* W is held while I is taken (the writer's cut and close); the thread,
  which takes I, never takes W, and the listener it calls
  (`computeRules`: D; `handleStreamException`: B, and I through
  `close()`) is called with neither B nor I held. D is held while B is
  taken (`sync` calls `flushSoon`), never with I.

So the order is W before B, W before I, D before B, I before S: no
cycle. The waits on B's condition (`wait()` in `append`, `close`,
`consume`) release B and are never made holding I.

### Readers are not blocked by I/O

`read()` takes B for the decision and a copy from the ring, and calls
`stream.read` holding nothing; it never takes I. B is never held during
a call to the stream below, as before. `getFirstPos()` takes no lock. So
a reader never waits for an append, a force, a cut or a close.

### P7 on every failure path

* A failed append (an IOException, or anything else, wrapped as since
  005-32): I is released in a `finally`, then `stopAfterFailure` as
  before: the failure is set, the thread stops, the listener is told,
  the storage fails (015-81, 015-35).
* A failed pending cut, or a `getFirstPos()` after it that throws: the
  same, in the same `try`; the flush is not published.
* A failed writer's cut: I released in a `finally`, the exception to the
  caller as before (Reclaim's `StreamIoException` fails the database);
  the kept first position stays the one before the cut.
* A failed close: `closeStream` as before (015-78, 015-81), the close
  made holding I.
* A thread that dies holding I (an Error in a call below): the `finally`
  releases I, so no other thread waits for ever.

### At close, and on a failed append

* `close()` by the writer: B as before (what is buffered is written),
  `stop()`, the join of the thread (whose `finally` closes the stream
  below, holding I), then `closeStream` holding I again: the two closes
  were one after the other already; now a cut cannot run beside either.
* A failed append: the thread releases I before it tells the listener;
  `handleStreamException` closes the buffer on the thread, holding I for
  the stream's close, so a writer's cut that passed `StorageManager`'s
  error check just before the error was set is made before that close
  or after it, not beside it (after it, on a closed stream, it throws as
  before). A `close()` from a reader (a failed `StorageManager.read`) is
  serialized the same way.
* `stop()` alone: the thread closes the stream below as it ends, holding
  I; a later cut of a bare `BufferedStream` waits for that close and
  meets a closed stream, as before (`StorageManager` refuses it: its
  error is set first).

### Tests

Harness 6.3's `testOneWriterBufferedStream` and
`testOneWriterStorageManager`, and its workloads, with "015-80" taken
out of `StreamContract.SKIP`: they fail before the fix and pass after it.
They do not reach the thread's close or its pending cut beside a
writer's cut: `BufferedStream.testWriterCutBesideThreadsCutAndClose`
holds each of those in a `StrictStream` hook while a writer cuts, and
fails before the fix and passes after it. `testFirstPosAfterCuts` pins
the kept first position, after a cut made at once and after a kept cut
(it passes before and after).

The stream's bytes are unchanged (P2): the appends and their order are
the same; only when a cut is made relative to an append changes. No
setting, thread, timer or global state.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. The harness of 018-02 (the stream contract, 018-01, section
6.3) catches it: `StorageContractTester.testOneWriterBufferedStream` and
`testOneWriterStorageManager` force R5-F5's order on a `StrictStream` and
fail and name 015-80, and so do the workloads, most runs. The harness
also counts `getFirstPos()`, which the Javadoc puts under the write lock
too: `BufferedStream.getFirstPos()` calls the stream below beside the
thread's append, the same fault; a fix that leaves it still fails the
harness, under 015-80. Its fix removes the skip line "015-80" from
`StreamContract.SKIP`.


2026-11-06. Done in night 006-12, option 2 as argued above. Verified
first: with "015-80" out of `StreamContract.SKIP`, on the code before the
fix, `StorageContractTester` failed 4 of 6 tests:
`testOneWriterBufferedStream` and `testOneWriterStorageManager` (OVERLAP,
a cut and a `getFirstPos()` beside the thread's append),
`testWorkloadBufferedStream` ("GET_FIRST_POS in thread main overlaps
APPEND in thread BufferedStream-consumer-103") and
`testWorkloadStorageManager` (PRETRUNCATE beside APPEND); and the new
`BufferedStream.testWriterCutBesideThreadsCutAndClose` failed in both of
its cases: "PRETRUNCATE in thread BufferedStream-test-writer overlaps
PRETRUNCATE in thread BufferedStream-consumer-59", and, run first, the
same beside CLOSE. After the fix all pass, and so do the long workloads
(`bergdb.dev.Night -c StorageContractTester`, 20 seeds, 20 s).

* Fix, in `BufferedStream` only: `ioLock`, a fair `ReentrantLock`, held
  for each `stream.append` of a flush (`appendToStream`), each cut, the
  writer's and the thread's pending one, with the read of the first
  position after it (`cutStream`), and the close (`closeStream`).
  `getFirstPos()` returns the kept `firstPos` (volatile; set in the
  constructor and by `cutStream`). Failures are handled as before, after
  the lock is released.
* Javadoc: the class (one call at a time below), `ioLock`, `getFirstPos`,
  `pretruncate` (a cut at or before the flushed bytes waits for an
  append in progress, at most one).
* Reach: internal. A cut of reclaim may now wait for one append of the
  storage thread and its force, on a commit's path (section "The cost").
  010-01: no setting, thread, timer or global state; the stream's bytes
  are unchanged (P2); P1 as argued in "The cost"; P7 as in "P7 on every
  failure path".


2026-11-06. Landed on `main` at 01:16 after review R4 of night 006-12
(`/Users/f/fl/bench/006-12/review-r4.md`): verdict land, no A or B
finding; R4 confirmed by runs that each part of the fix (the lock on cuts
and appends, the kept first position, the lock on the close) has a test
that fails without it. Its C findings:

* C1, for Frans's decision, not done: Reclaim's cut now waits for the
  thread's append and its force, holding the write lock, and under steady
  writes most cuts will; an append is up to 5 MB (half the default
  buffer), above the 2.5 MB of the figures in "The cost", and on s1 a
  force can take seconds; P1's "Where BergDB stands" in 010-01 has no line
  for it. R4's possible fix: Reclaim's cut tries the lock (`tryLock`) and,
  when the thread is appending, keeps the cut to its next commit (the
  writer still makes the cut, so the kept first position stays exact),
  with a fall-back to the plain lock after some growth.
* C2, fixed in a follow-up commit (test code and words): the class
  Javadoc states the rule that the kept first position depends on (the
  stream given to it is cut, appended to and closed only through it), and
  `DbTesterFailure.testGetTransBelowTheCut` cuts through the storage's
  buffer, as reclaim does, not the `CutStream` below it, and checks the
  database's first position after the cut. It still fails on the fault it
  was written for (011-04, W1): with `Db.getTrans`'s branch for a read
  below the cut taken out, "DbFailedException: A read failed on the
  storage"; it passes with it.
* C3, fixed in the same commit: `testWriterCutBesideThreadsCutAndClose`
  has a `CutStream` below the close, so its first-position check compares
  the cut, 80, with the kept value; below the thread's cut it keeps a
  `MemoryStream` (a `CutStream` refuses the writer's later, lower cut).


2026-11-06, 09:47. C1 decided by Frans ("As recommended.", 006-12,
section 8, point 2): a line under P1 in 010-01, and 019-36 to measure the
cut's wait on F53 and s1 and, if it is over the target, R4's `tryLock`
fix.

State (night 006-12)
--------------------

2026-11-06, 01:20. Clone `/Users/f/fl/bench/006-12/f80`, branch `w1-f80b`
(from `main` at 33a81b9, the fix landed): the follow-up for R4's C2 and
C3 (test code and words), gated with `before-commit.sh`, one commit. C1
waits for Frans.
