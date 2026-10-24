005-36. Fix: DbTester.testCrash3 has never tested a truncation
===============================================================

Status: open. Kind: fix. Created 2026-10-24.

Found on 2026-10-23 in 005-29, by Claude (Opus 5.5, Claude Code), among
the tests that use `MemoryStream.truncate`; checked again on `685e895`.
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

So it has tested no truncation; the source of 2017 (`195cf88`) has the
same lines. It checks only that a key never written is not found.

Started on the copy, it fails on every run (3 of 3 on `685e895`). It takes
its first length, `size1`, as `testDb` returns, before the buffer (10 ms)
has written anything: `size1` is 0, and the lengths are 751, 676, ...,
226, 151, 76 and 1. The last four cut the new database's creation, its
first meta block (bytes 0 to 127) or its first transaction (128 to 263),
which is 005-33's case. The start at 226 throws `StreamFormatException`:
"Transaction at start pos 128 is not committed (its last byte is 0)."
Before 005-28 it hung there.

A start at each length of the test's stream, by a probe on `685e895`:

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
passes, 3 of 3 runs on `685e895`, at the lengths 751, 703, ..., 271. A cut
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
