005-28. Fix: startup loops for ever on a failed transaction at its start
========================================================================

Status: done (2026-10-23). Kind: fix. Created 2026-10-23.

Found on 2026-10-22 in 005-11, by Claude (Opus 5.5, Claude Code), with
the probe P9 ([11-replication/report.md](11-replication/report.md),
"P9"). Added at Frans's request ("add 005 entries for the bugs").


The issue
---------

`NodeStream.TransIterator.next` (NodeStream.java:317) loops for ever when
the first transaction at its start position is a failed one: its last byte
is 0, as recovery's zero fill leaves a torn transaction. It skips the
transaction with `continue start` (:362); since no transaction has been
counted yet (`transCount == 0`, :320), it goes back to the start position
(:322) and reads the same transaction again. A startup that reads from
there (`Db.getStartupPosFromLastTransaction`, `Db.readTransactions`) then
uses a core at 100 percent and never returns, with the write lock held.
`Db.getTrans` uses the same iterator.

In P9 ([11-replication/runs/p9-diverge.txt](11-replication/runs/p9-diverge.txt),
the first case; the same on `78cc5f3`), a start with a main and a replica
of two histories copied the replica's last transaction onto the main, after
the main's zero-filled one; that transaction named the zero-filled one as
its startup position. The database hung at startup, and so did every later
start of that main.

In one history it does not happen, as far as reading the code shows: a
transaction's startup position is that of a committed transaction written
before it (`TransSeq.take`), so complete in any prefix that has it; and a
meta block names the last transaction appended before it
(`NodeStream.appendNodes` sets it after the append). So only a damaged or
mixed stream meets it. (Not so: a crash in a new database's first
transaction meets it too; see Outcome.) Such a stream should make the
database fail with an error that says what is wrong, not hang.


The fix, proposed
-----------------

When the transaction at an exact start position is not committed, throw a
`StreamFormatException` that names the position: a startup position must
name a committed transaction, and stepping on would start from a state that
no transaction left. The iterator that starts at the last transaction
before a position (`exactStartPos` false, used by `NodeStream.print` and a
test) steps on to the next transaction instead of going back.


Done when
---------

* A unit test: a stream whose transaction at the start position is a failed
  one makes the iterator, and a startup from that position, throw
  `StreamFormatException` (with a time limit in the test, as today it
  hangs).
* P9's first case (005-11's probe `diverge`) fails at startup with that
  exception.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Size and order
--------------

S. Any time; independent of 005-11's decision. With 005-11's option B, its
fix 3 keeps two histories apart; this entry keeps a damaged stream from
hanging the database.


Outcome
-------

2026-10-23, by Claude (Opus 5.5, Claude Code), as proposed.
`NodeStream.TransIterator.next` finds its first transaction once: a new
field, `started`, set when a transaction has been read, replaces
`transCount == 0`, which stayed true after a failed transaction. When the
transaction at an exact start position is not committed, `next` throws a
`StreamFormatException` that names it: "Transaction at start pos 7273376
is not committed (its last byte is 0)." The exact start positions are
those of startup (`Db.getStartupPosFromLastTransaction`,
`Db.readTransactions`) and of `Db.getTrans`. The iterator from the last
transaction completed before a position (`NodeStream.print`, a test) steps
on to the next transaction. Nothing else changes: the code differs from
the old only where the old one looped, so no level script was run.

Found on the way: it happens in one history too. A crash while a database
is created, in its first transaction (the primordial one, after the first
meta block), leaves a stream whose meta block names no transaction.
Startup then starts at the first transaction, which recovery has
zero-filled, and every later start hung. Now such a database fails to
start with that exception, at position 128. It holds no committed
transaction, so nothing is lost when its files are removed and it is
created again. A crash that leaves the first meta block alone already
failed ("No transactions in startup transaction set."). Not done, for
Frans to decide: a start could create such a database again, as it does
for an empty stream.

Tests, in `NodeStreamTester`, each run in a thread with a time limit of
10 s; without the fix, all three are still running after 10 s
([runs/unit-without-fix.txt](28-fix-trans-iterator-loop/runs/unit-without-fix.txt)):

* `testTransIteratorAtFailedTrans`: a node stream with a transaction cut
  before its last byte and recovered, and a committed one after it. The
  iterator from the first one's exact position throws and names it; the
  iterator from position 0 gives the second one.
* `testStartupPosAtFailedTrans`: P9 in small. Four transactions with a
  startup distance of 10 bytes, so that the last one names the one before
  it as its startup position; that one's last byte is set to 0, as
  recovery leaves it. Startup throws and names it.
* `testCrashInPrimordialTrans`: a new database cut after 1, 4 and 5 bytes
  of its first transaction, in its middle and before its last byte.
  Startup throws and names position 128.

P9 (005-11's probe `diverge`, unchanged, on `f206e58` with the fix): the
first case's start with the main and the replica fails at once with that
exception, at 7273376, the transaction that the main's recovery
zero-filled; the second and third cases are as before
([runs/p9-diverge.txt](28-fix-trans-iterator-loop/runs/p9-diverge.txt), 9 s
instead of 129). In that run the main alone then started, with its own
2998 transactions: the failed start had copied the replica's tail into
the main's buffer, and the probe looked before the buffer was written to
the main's files. With a pause of 2 s after the failed start, the main
has the tail and fails alone too, with the same exception
([runs/p9-first-case-wait.txt](28-fix-trans-iterator-loop/runs/p9-first-case-wait.txt)).
A start that throws does not stop its storage: the buffers' threads go on
and write what startup appended. That is so for any start that fails, and
is not changed here.

`before-commit.sh`: BEFORE COMMIT OK (977 unit tests, 63 f-tests).
