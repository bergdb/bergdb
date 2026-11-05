018-02. Harness 6.3: the stream contract
========================================

Created 2026-11-05 by Frans Lundberg, who chose harness 6.3 of 018-01 as
the first (2026-11-05, 10:27). Built by Claude (Opus 5.5, Claude Code)
for the day's session bergdb-e8.

**Status: built; runs in `before-commit.sh`'s unit tests and in
`night.sh`'s night tests.** It fails on each of the six known faults of
its class (018-01, section 6.3), and on one more that it found, 019-02.
With the skip list (section 4) it passes on `main`.


## 1. What it checks, and why

`AppendOnlyStream` is the interface between the storage and the streams:
`StorageManager` and `BufferedStream` implement it and use it, and
`FileStream`, `MemoryStream` and `SalsaStream` are under them in a
database. Its Javadoc is the contract. Each of the six known faults
breaks one of its promises; a review found each by reading one
implementation. The harness checks every promise on every implementation,
so that a breach no review has met is found too.

The promises, from the Javadoc of `AppendOnlyStream` (and of
`ReadBelowFirstPosException`):

* `append()`: when it returns, the bytes can be read and the length has
  grown by them; `IllegalArgumentException` for a negative length or one
  greater than the array.
* `read()`: returns exactly the bytes appended, which are never changed;
  `IllegalArgumentException` for a negative length or one greater than
  the array; `EOFException` when there is not enough data;
  `ReadBelowFirstPosException` for bytes before the first position.
* `getLength()`: the bytes ever appended; it never decreases, and a cut
  does not change it.
* `getFirstPos()`: 0 in a new stream; after a cut, larger perhaps, but
  never past the cut, since the bytes from the cut on are still used.
* `pretruncate()`: a position up to the length is taken (how much is
  discarded is the stream's choice); one beyond it is refused, with
  `IllegalArgumentException` or `IOException`, and the stream is left as
  it was. `BufferedStream` holds such a position until it has written
  that far; `OneFileStream` ignores every position.
* `seekFirstPos()`: only before any append; `IllegalStateException` if
  the length is greater than the position.
* CONCURRENCY: `read()` from many threads; every other call, `getLength()`
  and `getFirstPos()` too, by threads that hold one write lock. An
  implementation may rely on it.

The harness has two parts:

* **The contract tester** runs the same checks on every implementation,
  each check on a new stream, at the interface's edges (section 2.2).
* **The strict stream** checks a layer from below: `BufferedStream` and
  `StorageManager` run on it, and it checks each call that they make to
  the stream under them, and each answer of that stream (section 2.1).


## 2. The classes

Test code only, in `java/src`, as the repository's tests are; registered
in their package's `Pack`. Nothing in the production code changed.

| Class | Package | What |
|---|---|---|
| `StrictStream`          | `bergdb.stream`  | The strict stream (2.1) |
| `StreamContract`        | `bergdb.stream`  | The checks (2.2), the skip list and the entries (4) |
| `StreamContractTester`  | `bergdb.stream`  | Nano tests: this package's streams, `StrictStream` |
| `StorageContractTester` | `bergdb.storage` | Nano tests: `BufferedStream`, `StorageManager` (2.3) |


### 2.1. StrictStream

A wrapper for tests. Each call is checked against the Javadoc, and a
breach throws `StrictStream.Breach` (an `AssertionError`) at once. Every
breach is also kept (`breaches()`): a breach thrown in a thread of the
code under test is caught there (`BufferedStream`'s thread turns what a
flush throws into a failed stream), and the test asserts after the run
that there was none. Its kinds:

* The caller's side, the layer above: OVERLAP, a call but `read()` while
  another is in progress, in another thread (one writer at a time, as
  R5-F5's test stream checked); ARGUMENT, a negative length or position,
  or a length past the array; CUT_BEYOND_LENGTH; SEEK_AFTER_APPEND.
* The stream's side, the one below: LENGTH, a length that is not the bytes
  appended or that decreases; FIRST_POS, a first position that decreases
  or passes the length or the last cut; NOT_EOF, a read past the end that
  returns or throws another `IOException` than `EOFException`; LOST, a
  read of bytes that are there that throws `EOFException` or
  `ReadBelowFirstPosException`; BYTES, a read that returns other bytes
  than those appended (the first 16 MB are kept to compare); UNCHECKED, an
  unchecked exception for a call made by the rules.

A read past the end counts the bytes of an append in progress, which a
read may see first; after a failed call or `close()`, a read may fail as
the stream likes.

For harness 6.2 (failures and interrupts), it has a `Hook`: it sees each
call, with its number, before the stream below does, and for a call but
`read()` while the call holds the writer's place. A test can hold a call
there (the one-writer test does), count calls, or throw an `IOException`,
an unchecked exception or an `Error`. 6.2 itself is not built.
`tolerate(kinds)` makes breaches of those kinds kept but not thrown: a
workload goes on past a known fault (section 4).


### 2.2. The contract tester

`StreamContract.check(impl, results)` runs these checks on an
implementation, each on a new stream from its factory, which it closes:

1. An empty stream: length 0, first position 0, a read of 0 bytes, and
   `EOFException` for one of 1 byte.
2. Length 0: appends and reads of 0 bytes, also at the end.
3. Appends and reads: 1 to 70,000 bytes, read back whole and in parts.
4. A negative append, and 5. an append longer than its array: refused
   with `IllegalArgumentException`, the length unchanged, the bytes
   readable, the next append works.
6. A negative read, and 7. a read longer than its array:
   `IllegalArgumentException`, and the stream goes on.
8. A read past the end, three of them: at the end, across it, beyond it;
   each `EOFException`, each on a new stream (a `StorageManager` fails
   at a read's `IOException`, by design).
9. A read below the first position, after a cut at 2.1 MB of 2.5 MB:
   `ReadBelowFirstPosException`, and the bytes from the cut are read.
10. Cuts within the length: at 0, 300, 300 again, 999 of 1,000; the
    length unchanged, the first position not past the cut, the bytes from
    the cut read back.
11. A cut at the length: on an empty stream, and at 3 of 3 bytes.
12. A cut beyond the length: refused and the stream as it was (or held,
    or ignored, for `BufferedStream`, `StorageManager` and
    `OneFileStream`); the stream goes on.
13. `seekFirstPos()` on a new stream, and after an append.
14. `close()`.

And `FileStream`'s file-size limit (`fileSizeLimit()`): with
`setMax2G(true)`, no file over 2 GB. R2-F4's probe reached the state
with 400 restarts that each wrote 100 MB; the check makes that directory
directly, 400 files of 100 MB, so that a start chooses 100 MB files from
the last two, and the size rule then picks 10 GB, a quarter of the 40 GB
the stream holds. Then 2.1 GB of appends. The files are sparse, through
`FileStreamIo` (the test boundary that `FileStream` has had since
2026-10-14): writes extend the file and write nothing, and forces do
nothing. The check takes 0.07 s and no disk space, so it needs no hook
in the production code, and no real 2^31-byte file, which would have put
it in the night. On a file system without sparse files (a 1 GB file
takes more than 500 MB of space) it says so and does not run.

The other `FileStream` checks use a `FileStreamIo` without forces:
durability is not the contract's subject, and forces cost tens of
milliseconds each.

Each check's data is a byte function of the stream position, so a read
anywhere is compared with what was appended.


### 2.3. BufferedStream and StorageManager on the strict stream

`StorageContractTester` runs, for each of the two:

* **The contract tester**, on a `MemoryStream`, with a buffer of 10,000
  bytes and 10 ms.
* **One writer, R5-F5's forced order** (015-80). Under the strict stream,
  on a `MemoryStream` with 100 bytes, the hook holds the buffer's first
  append to the stream below. The writer, holding the write lock, then
  cuts at 50, below what has been flushed, in a thread of its own; and,
  in a second run, asks for the first position. Either must wait for the
  append, or leave the call to the buffer's thread; on `main` each calls
  the stream below beside the append, and the strict stream throws
  OVERLAP. The writer's thread is joined after 200 ms and the append
  released: a fix that makes the cut wait is not taken for a deadlock.
  The Javadoc puts `getFirstPos()` under the write lock too, and
  `BufferedStream.getFirstPos()` calls the stream below from the writer
  while the buffer's thread appends: the same fault, and the same entry.
* **A workload**, 150 ms, on the strict stream on a `MemoryStream`: a
  writer that, with the write lock, appends 1 to 3,000 bytes at a time,
  cuts every 25 appends, asks for the length and the first position
  every 10, and syncs every 40 (`sync()`, or `flushSoon()` for the
  buffer); and two readers that read what has been appended and compare
  it. Each breach of the strict stream fails it, and so does a read
  that returns other bytes, or fails, but below a cut. While 015-80 is
  in the skip list, OVERLAP is tolerated, kept and skipped, so that the
  workload checks the rest; without it, the breach is thrown at once.
  On `main` the workload meets OVERLAP in most runs: a cut or
  `getFirstPos()` beside the buffer's append.

The stream below is a `MemoryStream`, not a `FileStream`, in these runs:
they check the layer above, and a `FileStream` brings its own faults
(015-31 at a cut at the flushed length), which the contract tester
checks on it directly.


### 2.4. The implementations

The contract tester runs on `FileStream`, `MemoryStream`, `OneFileStream`,
`CutStream`, `SalsaStream` (on a `MemoryStream`), `BufferedStream` and
`StorageManager`. Not on:

* `DummyStream`: it keeps only its first 10,000 bytes and fails reads
  past them, by design (its Javadoc), for tests that need no bytes.
* `ReadOnlyStream`: it refuses every append and cut, by design.
* `StrictStream`: it refuses what the contract lets a caller do (a
  negative length is its breach, not an `IllegalArgumentException`); its
  own tests check each kind (`testStrictCaller`, `testStrictWrapped`).
* The test streams inside other tests (`DbTester.SlowStream`,
  `DbTesterFailure.FaultStream` and others): each wraps a `MemoryStream`
  or a `FileStream` to slow or fail calls for one test.

`seekFirstPos()` is checked where it is supported: `MemoryStream`,
`OneFileStream`, `CutStream` (through `MemoryStream`) and
`StorageManager` throw `UnsupportedOperationException`. The Javadoc does
not say that it is optional, but it was added for replication, which is
gone (005-11), and only `FileStream`'s tests use it.


## 3. Where it runs, and its cost

All but one test are in the Nano group "unit": 14 tests, 0.6 s together
(the workloads 0.15 s each, the file-size limit 0.07 s, the rest 0.1 s or
less). `before-commit.sh` runs the unit tests beside the f-tests, which
take the longest, so the harness adds nothing measurable to its time:

| `before-commit.sh` on F53, 2026-11-05 | Unit tests | F-tests | BEFORE COMMIT OK |
|---|---|---|---|
| Two gates of W1, before the harness | 1,134 in 25.7, 25.9 s | 63.4, 63.9 s | 103, 103 s |
| Two gates of this item, with it     | 1,148 in 26.9, 26.1 s | 65.1, 64.0 s | 104, 104 s |

The unit tests take 10.4 s alone (11.5 s with the harness) and about 26 s
beside the f-tests; the f-tests set the time. The difference of 1 s is
within what one gate differs from the next.

`stress/core-build.sh`, a step of `night.sh`, runs them too, on the Core
Layer built alone (CORE BUILD OK, 746 unit tests in 9.5 s).

`testWorkloadsLong`, in the Nano group "night", runs the workload for 20
seeds, 1 s each, alternately on `BufferedStream` and `StorageManager`:
20 s in `night.sh`'s step night-tests, which runs every Pack's night
group. So the harness needed no script and no step of its own.

From `java/`:

```sh
./unit.sh -c ContractTester                          # the unit tests, 0.6 s
./night.sh tests -c StorageContractTester            # the long workloads, 20 s
java -ea -Dbergdb.contract.skip=none -cp build/bergdb.jar bergdb.dev.Unit -c ContractTester
                                                     # nothing skipped: the known faults
```


## 4. The skip list

Landing option (a), as Frans chose: the harness skips the known faults
of a list, so that it passes on `main` today. The list is
`StreamContract.SKIP`, one line per entry:

```java
static final String[] SKIP = {
    "015-26",
    "015-31",
    "015-33",
    "015-79",
    "015-80",
    "015-83",
    "019-02",
};
```

`StreamContract.FAULTS` says which entry a failed check is: the
implementation, the start of the check's name, the entry. When a check
fails:

* its entry is in SKIP: the test prints "Known fault 015-31, skipped:"
  and the failure, and passes;
* its entry is not in SKIP: the test fails, and names the entry;
* it has no entry: the test fails with "No entry, a new fault:".

**A fix removes its own line.** A line whose checks all pass fails the
test: "015-31: in the skip list, StreamContract.SKIP, but its checks
pass; its fix removes the line". So the fix of 015-31 makes
`StreamContractTester.testFileStream` fail until the line `"015-31",`
is gone, and the harness then checks the fault for good. The workloads
do not count for this, as their one-writer breach depends on timing;
the forced order does.

With `-Dbergdb.contract.skip=none` nothing is skipped.


## 5. The evidence

On the code of 4f0c1f0 (`main`) with the harness, from `java/`, every
known fault named, nothing skipped:

```sh
./build.sh
java -ea -Dbergdb.contract.skip=none -cp build/bergdb.jar bergdb.dev.Unit -c ContractTester
```

The output, cut to one line per fault and check (44 lines in all; the
known faults' lines are those printed after "Known fault ..., skipped:"
in a run with the list):

```text
015-26: FileStream, a negative append: java.lang.AssertionError: append(byte[1], 0, -1) threw
  java.lang.AssertionError: 2 != 3, expected IllegalArgumentException (at stream.FileStream$DbFile.append:1512)
015-31: FileStream, a cut at the length, 0: bergdb.common.Bug: Unexpected newSize: 0. pos=0,
  kfiles.length=1 (at stream.FileStream.pretruncate:517)
015-31: FileStream, a cut at the length, 3: bergdb.common.Bug: Unexpected newSize: 0. pos=3, ...
015-33: FileStream, the file-size limit: java.lang.AssertionError: with setMax2G(true), the file
  00000000400000.bergdb has 2100000000 bytes, more than 2 GB
015-79: BufferedStream, a negative append: java.lang.AssertionError: append(byte[1], 0, -1) returned,
  expected IllegalArgumentException
015-79: StorageManager, a negative append: ... returned, expected IllegalArgumentException
015-80: BufferedStream, one writer: a cut during a flush: bergdb.stream.StrictStream$Breach: OVERLAP:
  PRETRUNCATE in thread StorageContractTester-writer overlaps APPEND in thread BufferedStream-consumer-46
015-80: BufferedStream, one writer: getFirstPos() during a flush: ... OVERLAP: GET_FIRST_POS in thread
  StorageContractTester-writer overlaps APPEND in thread BufferedStream-consumer-48
015-80: StorageManager, one writer: a cut during a flush: ... OVERLAP: PRETRUNCATE ... overlaps APPEND
015-80: StorageManager, one writer, in the workload, seed 2: ... OVERLAP: APPEND in thread
  BufferedStream-consumer-75 overlaps PRETRUNCATE in thread main: one writer at a time
015-80: StorageManager, one writer, in the workload, seed 2, then the writer: java.io.IOException:
  The flush failed (the cause).
015-83: BufferedStream, a read past the end, 1 bytes at 10 of 10: java.lang.AssertionError:
  read(10, 1) of 10 bytes threw java.io.IOException: Cannot read 1 bytes at position 10, stream size
  is 10., expected EOFException (at storage.BufferedStream.read:373)
015-83: StorageManager, an empty stream: java.lang.AssertionError: read(0, 1) of an empty stream threw
  java.io.IOException: Cannot read 1 bytes at position 0, stream size is 0., expected EOFException
019-02: FileStream, a negative read: java.lang.AssertionError: read(0, byte[4], 0, -1) threw
  java.lang.IndexOutOfBoundsException, expected IllegalArgumentException (at stream.FileStream$DbFile.read:...)
019-02: SalsaStream, a negative append: java.lang.AssertionError: append(byte[1], 0, -1) returned,
  expected IllegalArgumentException
FAILURE, total: 15, failed: 12. Time: 0.5 s.
```

The run with seed 2 shows 015-80's effect on a stream that relies on one
writer: the buffer's append met the cut, the flush failed, and the
storage with it.

The same without the property: `SUCCESS, 15 successful tests in 0.6 s.`
And the long workloads, nothing skipped, on 20 seeds:
`./night.sh tests -c StorageContractTester` with the property: every
failure is 015-80's (OVERLAP, and the failures of the workload after
it), none other.

Per fault, each caught, and each failure names its entry:

* 015-26: `testFileStream`, "a negative append": `AssertionError: 2 !=
  3` from the assert in `FileStream.DbFile.append` (with `-ea`; without,
  the append returns).
* 015-31: `testFileStream`, "a cut at the length", at 0 and at 3:
  `Bug: Unexpected newSize: 0`.
* 015-33: `testFileStreamSizeLimit`: a file of 2,100,000,000 bytes with
  `setMax2G(true)`.
* 015-79: `testBufferedStream` and `testStorageManager`, "a negative
  append": it returned.
* 015-80: `testOneWriterBufferedStream` and
  `testOneWriterStorageManager`: OVERLAP, a cut and a `getFirstPos()`
  beside the buffer's append; and the workloads.
* 015-83: `testBufferedStream` and `testStorageManager`, "a read past
  the end" (all three) and "an empty stream": `IOException`, not
  `EOFException`.
* 019-02, new: the argument checks of every stream but `MemoryStream`'s
  appends (section 5.1).


### 5.1. A fault it found: 019-02

`read()` and `append()` refuse a negative length, or one greater than
the array, with other exceptions than the `IllegalArgumentException`
that the Javadoc promises, or with none: `IndexOutOfBoundsException`
(`FileStream`, `OneFileStream`), `ArrayIndexOutOfBoundsException`
(`MemoryStream`'s and `CutStream`'s reads, `SalsaStream`,
`BufferedStream`), `NegativeArraySizeException` (`SalsaStream`'s
negative read), `AssertionError` (`BufferedStream`'s read longer than
its array, with `-ea`); `SalsaStream` and, as 015-79, `BufferedStream`
return from a negative append. Each leaves the stream as it was (the
tester checks that), so only the exception is wrong. No layer of BergDB
passes such a length: the strict stream under `BufferedStream` and
`StorageManager` met none. Registered as 019-02, a fault of the Core
(018-01, W3), with its line in SKIP.


## 6. What it does not cover

* Durability and forces: `FileStream` runs without forces here. The
  power-loss tests (`FileStreamPowerLossTester`) and harness 6.2 are for
  them.
* Failures and interrupts in the streams: harness 6.2, through
  `StrictStream`'s hook.
* The implementations' own concurrency: the contract tester is one
  thread; the workloads run readers beside the writer only on the
  buffer, over a `MemoryStream`. `FileStream`'s readers beside its writer
  and cut have tests of their own (005-46); jcstress is 6.6.
* `FileStream` under `BufferedStream` on the strict stream, restarts and
  a stream's state across them, and positions near 2^63.
* That `pretruncate()` returns quickly, which the Javadoc asks but does
  not bound.
* A call after `close()`, which the Javadoc does not define;
  `BufferedStream` closes the stream below twice, which `FileStream`
  and `MemoryStream` accept.
* The strict stream in a database: `Db` on `StorageManager` on it, with
  reclaim, which 6.2's workload will add.


## 7. Log

2026-11-05. Built (W2 of 018-01, the first harness): `StrictStream`,
`StreamContract`, `StreamContractTester`, `StorageContractTester`. It
fails on the six known faults of 6.3 and found 019-02; the skip list has
the seven. In the unit tests (0.6 s, nothing added to `before-commit.sh`'s
time) and the night tests (20 s). BEFORE COMMIT OK.
