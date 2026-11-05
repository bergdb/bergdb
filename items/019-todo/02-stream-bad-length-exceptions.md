019-02. Fix: the streams refuse a bad length with other exceptions than IllegalArgumentException
================================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Frans: none.
Created 2026-11-05 by Frans Lundberg.

What: `AppendOnlyStream`'s Javadoc says that `read()` and `append()`
throw `IllegalArgumentException` for a negative length or one greater
than the array. The streams of `bergdb.stream` and `bergdb.storage` throw
other exceptions, or none, as the harness of 018-02 found:

* `FileStream`: `IndexOutOfBoundsException` for an append longer than its
  array, a negative read and a read longer than its array. Its negative
  append is 015-26.
* `MemoryStream`, and `CutStream` through it:
  `ArrayIndexOutOfBoundsException` for a negative read and a read longer
  than its array. Its appends are right.
* `OneFileStream`: `IndexOutOfBoundsException` for all four.
* `SalsaStream`: a negative append returns; `ArrayIndexOutOfBoundsException`
  for an append longer than its array and a read longer than its array;
  `NegativeArraySizeException` for a negative read.
* `BufferedStream`, and `StorageManager` through it:
  `ArrayIndexOutOfBoundsException` for an append longer than its array and
  a negative read; `AssertionError` (with `-ea`) for a read longer than
  its array. Their negative append is 015-79.

Why: found by the harness of 018-02 (the stream contract, 018-01, section
6.3), 2026-11-05, in its contract tester's checks "an append longer than
its array", "a negative read" and "a read longer than its array", and "a
negative append" of `OneFileStream` and `SalsaStream`. Each refusal leaves
the stream as it was (the tester checks the length, the bytes and the
next append), so only the exception is wrong; and no layer of BergDB
passes such a length (the strict stream under `BufferedStream` and
`StorageManager` met none). A fault of the Core (018-01, D1; severity C,
a wrong exception), which joins the goal's list (018-01, W3).

Frans: none.

Done when: `StreamContractTester` and `StorageContractTester` pass with
the line `"019-02",` removed from `StreamContract.SKIP` (018-02, section
4), and `before-commit.sh` prints BEFORE COMMIT OK.

First step: remove the line and run
`java/unit.sh -c ContractTester`: it lists every failing check. Then
check the arguments at the top of each `read()` and `append()`, before
anything changes, as `MemoryStream.append` does since 005-37. The negative
appends of `FileStream` (015-26) and of `BufferedStream` and
`StorageManager` (015-79) are their own entries.


Log
---

2026-11-05. Registered by the agent that built 018-02's harness, for the
day's session bergdb-e8.

2026-11-05. Done in night 006-12. Harness 6.3 is the test: with the line
"019-02" removed from `StreamContract.SKIP`, `java/unit.sh -c
ContractTester` failed 7 of its 15 tests before the fix (the checks
listed under What: 21 checks, with `FileStream`'s, `BufferedStream`'s and
`StorageManager`'s negative appends already right since 015-26 and
015-79) and passes after it.

* Fix: a new `Util.checkRange(array, offset, length)` throws
  `IllegalArgumentException` for a negative offset or length, or an
  offset + length greater than the array's length; `read()` and
  `append()` of `FileStream`, `MemoryStream` (its read; its append checked
  since 005-37), `CutStream` (its read, before the cut's check),
  `OneFileStream`, `SalsaStream`, `BufferedStream` (in place of its read's
  assert) and `StorageManager` call it at their top, before anything
  changes. In `FileStream.append`, `BufferedStream.append` and
  `StorageManager.append` it takes the place of 015-26's and 015-79's
  check of a negative length, at the same place (after the failed-state
  checks), so their exceptions stay as they chose. `StorageManager` checks
  for itself, whatever its main stream does; an
  `IllegalArgumentException` is not an `IOException`, so the storage does
  not fail at it.
* The offset is checked too: `StrictStream` already took such a call as
  the caller's breach (`Kind.ARGUMENT`), and `MemoryStream.append`
  refused it. `AppendOnlyStream`'s Javadoc of `read()` and `append()` now
  names the offset, and says that the stream is left as it was. New test
  `Util.testCheckRange` for the offsets, which the harness does not try.
* Not changed: `DummyStream` (used by no code), `ReadOnlyStream` (passes
  its reads on), and the test streams in `BufferedStream`'s tester.
* Reach: no layer of BergDB passes such a range (the strict stream under
  `BufferedStream` and `StorageManager` met none). 010-01: no setting,
  thread, global state or format change; the stream's bytes are
  unchanged.
