019-02. Fix: the streams refuse a bad length with other exceptions than IllegalArgumentException
================================================================================================

Status: open. Kind: Fix. Frans: none.
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
