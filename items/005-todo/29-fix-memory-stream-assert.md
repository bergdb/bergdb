005-29. Fix: MemoryStream.copy fails an assertion at multiples of 1 MB
======================================================================

Status: open. Kind: fix. Created 2026-10-23.

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
