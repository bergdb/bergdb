005-28. Fix: startup loops for ever on a failed transaction at its start
========================================================================

Status: open. Kind: fix. Created 2026-10-23.

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
mixed stream meets it. Such a stream should make the database fail with an
error that says what is wrong, not hang.


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
