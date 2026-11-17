021-14. Fix: a read near Long.MAX_VALUE passed the storage's check of the end
=============================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: `BufferedStream.read` computes the last byte it reads as
`position + length - 1`, which overflows for a position within `length`
of `Long.MAX_VALUE`; the check against the stream's length then passes,
and the read takes bytes of the ring buffer, where
`AppendOnlyStream.read()` names `EOFException`. Found by the session that
ports the Core to C (012), by reading, not shown reachable: C refuses
such a read as past the end.

Why: a read past the end must throw `EOFException` (AppendOnlyStream's
contract, 018-02), and a read that returns bytes that are not there is a
wrong answer. 019-32's class, a damaged stream whose checksums are right,
gives a read the positions that its pointers hold.

Frans: none.

Done when: a unit test that calls `read` with such a position and length
directly; the same pattern sought in the other streams and readers of the
storage and the Core (`FileStream`, `MemoryStream`, `StreamContract`, the
node readers, the arithmetic of positions); whether a damaged stream with
right checksums can carry such a position to a read, said here; the
checks made without the overflow, such a read refused as a read past the
end; `BEFORE COMMIT OK` and `java/stress/level1.sh` under the gate lock.

First step: `BufferedStream.read(Long.MAX_VALUE - 2, dest, 0, 4)`.


Log
---

2026-11-09. Registered by coord-1109 from the finding of the C port, and
taken by its agent p14 (clone `clone-p14`, on main's ea1fa31).

2026-11-09. Done by p14: commit 2998875 in `clone-p14`, on main's
ea1fa31, to land. Severity: low; the database's outcome was right, its
cause not.

* Confirmed, by direct calls (probe `OverflowProbe`, below): of reads
  whose end overflows, none threw `EOFException`. With the database's
  default buffer (10 MB), each threw `ArrayIndexOutOfBoundsException`
  from `readFromBuffer` (lengths up to 199,872, the most that
  `RecoverableStream` reads at once); with some smaller buffers a read
  returned bytes of the ring buffer: 4 bytes at `Long.MAX_VALUE - 2` with
  a buffer of 128, 1,024 or 4,096 bytes, 32 bytes at
  `Long.MAX_VALUE - 22` with 100 bytes. The Core's `DbBuilder.stream`
  takes any buffer of 100 bytes or more.
* The same pattern elsewhere:
  * `MemoryStream.read`: `position + len > size` overflowed; the read
    returned with `dest` as it was (4 bytes at `Long.MAX_VALUE - 2`), or
    threw an `IOException` that is not `EOFException` ("stream not that
    large", 1 byte at `Long.MAX_VALUE`). Fixed. Under a `BufferedStream`
    such a read does not reach it (the buffer's check comes first), but
    `CutStream` and `SalsaStream` pass it on, and the class is public.
  * `StrictStream`, the tests' checker of the contract: its
    `end = position + len` overflowed, so an `EOFException` near
    `Long.MAX_VALUE` was taken for a LOST breach, and a read that returned
    was no NOT_EOF breach. Fixed.
  * `DummyStream`, a test stream outside the contract by design: an
    `ArrayIndexOutOfBoundsException`; now its own `IOException`.
  * `NodeStream.checkReadSize`: `RecoverableStream.getSpos(pos, size - 1)
    >= length` overflowed for a `pos` near `Long.MAX_VALUE`, and passed.
    Not reached once the reads are right (the read of the size at `pos`
    comes first), fixed anyway: `pos >= length` first.
  * Not affected: `FileStream` (a position past the end finds the last
    file, whose end is compared without a sum: `EOFException`),
    `OneFileStream` (`RandomAccessFile`: `EOFException`), `CutStream`,
    `SalsaStream` and `ReadOnlyStream` (they pass the read on),
    `StorageManager` (it passes the read on, and makes an unchecked
    exception of it a failed storage, 019-10), `RecoverableStream.read`
    (the stream below checks each part before the position moves on, and
    the step past a meta block cannot overflow), the transaction
    iterators (`tpos >= length` first, positions from a scan), `Spos` and
    `getSpos()` (their callers' positions are bounded).
* Can a damaged stream carry such a position to a read? Yes. A stream
  pointer is checked only for `Spos.isValidOrNull` (019-32:
  `StoredKeyNode.parse`, `KeyNode.validateStreamNode`, and `pointerPos <
  0` in `NodeCollection.followStreamPointer` and `followValuePointer`);
  nothing bounds it above, and an odd one is refused as a vpos. An even
  pointer near `Long.MAX_VALUE`, its node's checksum right, reaches
  `NodeStream.readNodeHeader` (32 bytes) or `readNode` (4 bytes, then the
  size), through `RecoverableStream` and `StorageManager`, to
  `BufferedStream`. Probe `PointerProbe` (harness 6.1's `LONG`, seed 1,
  021-11's two pointers set to `Long.MAX_VALUE` - 1, - 7 and - 29):
  before, the start refused the stream (a top node's skip pointer) or a
  read failed the database (a key node's pointer), with "The main
  stream's read threw java.lang.ArrayIndexOutOfBoundsException" as the
  cause; now with `EOFException`, "Cannot read 32 bytes at position ...",
  as for a pointer far past the end (`Long.MAX_VALUE - 4,294,967,295`:
  the same before and after). Harness 6.1's copies do not make such a
  pointer: its 8-byte values near `Long.MAX_VALUE` are odd, and a 4-byte
  field it sets leaves the other half of a pointer as it was. A read of
  ring-buffer bytes on these paths needs a buffer whose remainders fit
  (`Sim.java`: some sizes from 100 bytes up, for reads of 4 and 32 bytes
  at even positions; none at 100 KB or 10 MB).
* Fix, the comparisons without the sum: `BufferedStream.read`,
  `position > totalLength - length` (neither is negative, so no
  overflow; the same as `pos2 >= totalLength` wherever that sum did not
  overflow), and a read of 0 bytes returns after it, as it read nothing
  before (`pos2` underflows at `Long.MIN_VALUE`); `MemoryStream.read`,
  `position > size - len`; `StrictStream.pastEnd()`; `DummyStream`;
  `NodeStream.checkReadSize()`, `pos >= length` first.
* Tests, each failing before the fix:
  `BufferedStream.testReadPastEndNearMaxValue` (buffers of 100, 128,
  1,000 and 1,024 bytes, lengths 1, 4, 32 and 1,000, each position from
  `Long.MAX_VALUE - length` up: `EOFException`, and the stream as it was;
  before, `ArrayIndexOutOfBoundsException`); `StreamContract`'s "a read
  past the end" with 1 byte at `Long.MAX_VALUE` and 4 bytes at
  `Long.MAX_VALUE - 2`, for every stream of the contract (before,
  `MemoryStream`, `CutStream`, `SalsaStream`, `BufferedStream` and
  `StorageManager` failed); `StreamContractTester.testStrictWrapped`
  (before, LOST, and no NOT_EOF); `NodeStreamTester.testReadSizeNearMaxValue`
  (before, accepted).
* `releases/next.md`, Core API, a line.
* Probes: `/Users/f/fl/bench/2026-11-09/p14/` (`OverflowProbe`,
  `OverflowProbe2`, `PointerProbe`, `Sim.java`).

Runs, under the gate lock (2026-11-09, 14:19 to 14:25):
`BEFORE COMMIT OK (163 s)` (unit 1537, f 86, demos);
`java/stress/level1.sh`: `LEVEL 1 OK`.
