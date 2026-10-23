005-29. Fix: MemoryStream.copy fails an assertion at multiples of 1 MB
======================================================================

Status: done (2026-10-23). Kind: fix. Created 2026-10-23.

Found on 2026-10-22 in 005-11, by Claude (Opus 5.5, Claude Code): the
probe P2 copies `CutStream`s at cuts and met it
([11-replication/report.md](11-replication/report.md), "Found on the
way"). Added at Frans's request ("add 005 entries for the bugs").


The issue
---------

`MemoryStream.assertOk` (MemoryStream.java:75) takes the index of the last
array to be `streamLength / ARRAY_SIZE`. The arrays are made as bytes come
(`append`), so for a length that is a positive multiple of `ARRAY_SIZE`
(1,000,000) the last array is one before that, and for an empty stream
there is none. `copy()` asserts `copy.assertOk()`, so with assertions on
(`-ea`, as the tests run) a copy of such a stream throws `AssertionError`:

| Stream | `copy()` with `-ea` |
|---|---|
| empty | AssertionError |
| 1, 999,999, 1,000,001, 2,500,000 bytes | ok |
| 1,000,000, 2,000,000, 3,000,000 bytes | AssertionError |
| 2,500,000 bytes, cut at 2,000,000 | ok |
| 3,000,000 bytes, cut at 2,000,000 | AssertionError |

Test code only (`MemoryStream` is the in-memory stream of the tests), but
`CutStream.copy`, which `CrashTest`, the reclaim tests and the probes use,
calls it: a copy made when the length happens to be such a multiple fails
the test with a false alarm. P2 met it at a replica's length of 10,000,000,
half its 20 MB buffer. The probes run with assertions off in `MemoryStream`
(`-da:bergdb.stream.MemoryStream`, 005-11's `tools/run.sh`).


The fix, proposed
-----------------

The last array's index is `(streamLength - 1) / ARRAY_SIZE` for a stream
that is not empty, and an empty stream has no arrays: compare
`arrays.size()` with the number of arrays that hold bytes from the first
array's start to the end. One or two lines.


Done when
---------

* A unit test of `MemoryStream`: `copy()` of the streams in the table above
  succeeds, with assertions on, and the copies have the same bytes.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Size and order
--------------

S, any time.


Outcome
-------

2026-10-23, by Claude (Opus 5.5, Claude Code). The fix proposed above was
not enough alone: `truncate` and an append of 0 bytes made the array that
the old check expected, and the new check would have failed on them. Now
`MemoryStream` keeps exactly the arrays that hold bytes, from the first
array's start to the end of the stream, in three places:

* `assertOk` takes the index of the last byte's array,
  `Math.floorDiv(streamLength - 1, ARRAY_SIZE)`, as the last array's: -1,
  no array, for an empty stream.
* `truncate` keeps the arrays up to the last byte's. At a new length that
  is 0 or a multiple of `ARRAY_SIZE`, it kept an empty array after it.
* `append` of 0 bytes returns before its loop. On an empty stream the loop
  made an array, as `last` is -1 and `-1 / ARRAY_SIZE` is 0 in Java.

Test `MemoryStream.testCopyAtArrayBoundaries` (45 ms): the streams of the
table; an empty stream after an append of 0 bytes; and streams of
3,000,000 bytes truncated to 0, 1,000,000 and 2,000,000 bytes, one of them
cut at 2,000,000. Each stream is checked with `assertOk`, then `copy`, the
bytes of both, and an append to the copy. Without the fix the test fails
at the empty stream; with only `assertOk` changed, at the append of 0
bytes; without the change to `truncate`, in `truncate`'s own assertion.

Besides, with tools that are not kept: a random test of 40,000 steps of
appends, cuts, truncates and copies against a model, 16,420 of them at a
length that is a multiple of 1,000,000, found no invalid state and no
wrong byte; level 2's CrashTest step (25 rounds of 100 cuts, with `-ea`)
had 0 failures; and 005-11's P2, in its six configurations with
assertions on in `MemoryStream` too, ran to the end. Before the fix, each
of the six stopped at the false alarm, at a length of 2,000,000 (three of
them), 8,000,000, 10,000,000 or 36,000,000 bytes; the one at 10,000,000,
in the replica's buffer thread, left its run hanging.

Nothing changes for a database: `DatabaseBuilder.memory()` uses
`MemoryStream`, where an append of 0 bytes to an empty stream no longer
makes the first array before the first byte comes. 005-11's probes need no
`-da:bergdb.stream.MemoryStream` now; their scripts are left as they are.

`before-commit.sh`: BEFORE COMMIT OK on `f6bc3ce` with the change (975
unit tests, 63 f-tests), and on `948ec00`'s Java code with the change
(978 unit tests, 63 f-tests; 005-28 is in it).

Found on the way, not changed:

* `DbTester.testCrash3` ("Truncates complicated stream a few times") has
  started the database on the original stream since 2017, not on the
  truncated copy, so it tests no truncation. Started on the copy, it takes
  the first length before the buffer has written anything (0 in three
  runs), so four of its eleven cuts fall in the new database's first meta
  block and first transaction. Before 005-28 the start at 226 bytes hung
  there (005-28's case); with 005-28 such starts throw
  `StreamFormatException`: at a cut of 1 to 127 bytes, in the meta block,
  "Cannot recover stream without complete first meta block"; at 128, "No
  transactions in startup transaction set."; at 129 to 263, in the first
  transaction, "Transaction at start pos 128 is not committed". Every
  length from 264 to 751 starts and reads. With
  `db.sync(SyncLevel.STRONG)` before the first length is taken (then 264),
  the test passes on the copy (three runs, before 005-28).
* `MemoryStream` does not do two things that `AppendOnlyStream` says: it
  does not refuse a negative length to `append`, and a `pretruncate` past
  the length does not set the length (it throws
  `IndexOutOfBoundsException`, or leaves the first position past the
  length). Nothing calls them so: `BufferedStream` holds back a cut past
  what it has written, and `CutStream` refuses one.
