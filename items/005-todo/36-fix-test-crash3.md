005-36. Fix: DbTester.testCrash3 has never tested a truncation
===============================================================

Status: done (2026-10-24). Kind: fix. Created 2026-10-24.

Found on 2026-10-23 in 005-29, by Claude (Opus 5.5, Claude Code), among
the tests that use `MemoryStream.truncate`; checked again on `b61cf34`.
Added at Frans's request ("Add to 005.").


The issue
---------

`DbTester.testCrash3` (DbTester.java:1159), "Truncates complicated stream
a few times", writes three transactions, then truncates a copy of the
stream at eleven lengths and starts a database after each, but on the
original stream, not on the copy (:1186):

    MemoryStream mstream2 = mstream.copy();
    mstream2.truncate(newSize);
    Db db2 = testDb(mstream);

So it has tested no truncation; the source of 2017 (`0257e0b`) has the
same lines. It checks only that a key never written is not found.

Started on the copy, it fails on every run (3 of 3 on `b61cf34`). It takes
its first length, `size1`, as `testDb` returns, before the buffer (10 ms)
has written anything: `size1` is 0, and the lengths are 751, 676, ...,
226, 151, 76 and 1. The last four cut the new database's creation, its
first meta block (bytes 0 to 127) or its first transaction (128 to 263),
which is 005-33's case. The start at 226 throws `StreamFormatException`:
"Transaction at start pos 128 is not committed (its last byte is 0)."
Before 005-28 it hung there.

A start at each length of the test's stream, by a probe on `b61cf34`:

| Length | The start |
|---|---|
| 0 | creates the database |
| 1 to 127 | "Cannot recover stream without complete first meta block, length: L" |
| 128 | "No transactions in startup transaction set." |
| 129 to 263 | "Transaction at start pos 128 is not committed (its last byte is 0)." |
| 264 to 751 | starts, and the reads pass |


The fix, proposed
-----------------

Two lines in the test: start on the copy, `testDb(mstream2)`; and sync
the new database before the first length is taken,
`db.sync(SyncLevel.STRONG)` after `testDb(mstream)`, so that every cut
comes after the creation (`size1` is then 264). With both, the test
passes, 3 of 3 runs on `b61cf34`, at the lengths 751, 703, ..., 271. A cut
in the creation belongs to 005-33.

To decide with it: the test could also check what each cut keeps, the
values of the transactions before it, as `testCrash2` and `CrashTest` do.


Done when
---------

* `testCrash3` starts on each truncated copy, at lengths after the
  database's creation, and passes.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Size and order
--------------

S, any time; test code only. Independent of 005-33's decision.


Outcome
-------

2026-10-24, by Claude (Opus 5.5, Claude Code), as proposed, at Frans's
request ("fix all todo items of type Fix", "do what is proposed"). The two
lines in `DbTester.testCrash3`: the new database is synced,
`db.sync(SyncLevel.STRONG)`, before the first length is taken, so that
`size1` is the creation's 264 bytes; and each database starts on the
truncated copy, `testDb(mstream2)`. The cuts are at eleven lengths, from
751 down to 271 bytes, all after the creation. The test passes, 3 of 3
runs; without the sync it fails at once on the copy, with 005-33's case:
"Transaction at start pos 128 is not committed (its last byte is 0)." Not
done, as decided: a check of what each cut keeps.

`before-commit.sh`: BEFORE COMMIT OK (990 unit tests, 63 f-tests).
