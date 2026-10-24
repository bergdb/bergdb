005-37. Fix: MemoryStream takes a negative length and a cut past its end
========================================================================

Status: open. Kind: fix. Created 2026-10-24.

Found on 2026-10-23 in 005-29, by Claude (Opus 5.5, Claude Code); the
streams checked with probes on `685e895`. Added at Frans's request ("Add
to 005.").


The issue
---------

`AppendOnlyStream` promises two things that `MemoryStream`, the in-memory
stream of the tests and of `DatabaseBuilder.memory()`, does not do.

**A negative length to `append`.** The interface: "@throws
IllegalArgumentException if 'length' is less than 0 or greater than
source.length." `MemoryStream.append` does not check for a negative
length, and what happens depends on the stream:

| Stream | `append(b, 0, len)` | After it |
|---|---|---|
| empty, len -5 | `ArrayIndexOutOfBoundsException`: "arraycopy: length -5 is negative" | an array that holds no byte: `assertOk` fails, and so does `copy()` under `-ea` |
| 500 bytes, len -5 | the same | unchanged |
| 1,000,000 bytes, len -5; any stream, len -2,000,000 | returns, appends nothing | unchanged |

A negative offset gives `ArrayIndexOutOfBoundsException` too. The other
streams do not check the length either. `BufferedStream` and `SalsaStream`
return without appending. `FileStream` takes it off its file's length (6
after 10 bytes and a length of -4), so its next append fails ("is not of
expected length") and it refuses all I/O after that; under `-ea` the call
itself fails an assertion first. `OneFileStream` passes it to
`RandomAccessFile.write`, which throws `IndexOutOfBoundsException`.

**A `pretruncate` past the length.** The interface: "If the current
length of the stream is less than 'position', the data before 'position'
can be deleted and the stream length should be set to 'position'."
`MemoryStream.pretruncate` drops the 1,000,000-byte arrays before the
position's array and never sets the length:

| Stream | `pretruncate(p)` | After it |
|---|---|---|
| empty, p 500 | returns | length 0; appends go on at 0 |
| 2,500,000 bytes, p 2,999,999 | returns | length 2,500,000; appends go on there |
| 2,500,000 bytes, p 3,000,000 or 3,500,000 | returns | first position 3,000,000, past the length; every append throws `Bug` ("firstArray=2, firstArrayIndex=3") |
| empty, p 1,000,000 | `IndexOutOfBoundsException` | unchanged |
| 2,500,000 bytes, p 4,500,000 | `IndexOutOfBoundsException`, after it removed every array | no arrays, first position 0: `assertOk` fails, every read and append throws |

No stream does what the interface says. `FileStream` and `DummyStream`
throw `IllegalArgumentException`, `CutStream` an `IOException`,
`OneFileStream` ignores every cut, and `BufferedStream` holds back a cut
past what it has written until it has written that far.

BergDB itself does neither: `StorageManager` appends and cuts through
`BufferedStream`, which ignores a length below 1 and holds back such a
cut. A test, or an application that uses a stream directly, can.


The fix, proposed
-----------------

* `MemoryStream.append` refuses a negative length or offset with
  `IllegalArgumentException`, before it changes anything.
* `MemoryStream.pretruncate` refuses a position past the length with
  `IllegalArgumentException`, as `FileStream` does, before it changes
  anything.
* The Javadoc of `AppendOnlyStream.pretruncate` says what the streams do:
  a position past the length is refused (`BufferedStream` holds it back
  instead). The sentence that sets the length goes.

To decide with it: the same check of the length in the other streams,
`FileStream` first, as a negative length stops it.


Done when
---------

* Unit tests of `MemoryStream`: an append with a negative length or
  offset, and a `pretruncate` past the length, at the cases of the tables,
  throw `IllegalArgumentException` and leave the stream as it was
  (`assertOk`, its bytes, and an append after).
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Size and order
--------------

S, any time; `MemoryStream` and a Javadoc. The other streams, if Frans
wants them, are S too.
